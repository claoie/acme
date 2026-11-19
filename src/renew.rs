//! A renewal pass over every lineage, and issuing a new one.

use std::collections::HashMap;
use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::path::{Path, PathBuf};
use std::time::Duration;

use anyhow::{Context, Result, anyhow, bail, ensure};

use crate::acme::{self, Acme};
use crate::conf::{self, NewLineage};
use crate::keys::{CertInfo, Issued, KeySpec};
use crate::lineage::{self, KINDS, Lineage, write_atomic};
use crate::log::{error, info, utc, warning};

/// How long one certificate may take, end to end, before it counts as failed.
const LINEAGE_TIMEOUT: Duration = Duration::from_secs(300);

pub struct Settings {
    pub config_dir: PathBuf,
    pub ca_cert: Option<PathBuf>,
}

/// Whether a certificate is due, by the rules certbot 5 uses: renew once the
/// ACME Renewal Information time has passed; otherwise, with
/// `renew_before_expiry` set, once that much time is left; otherwise, without
/// ARI, once two thirds of its lifetime have passed (half, for certificates
/// that live under ten days). For a 90-day certificate that's 30 days left.
pub fn due(now: i64, not_before: i64, not_after: i64, renew_before_expiry: Option<i64>, ari_time: Option<i64>) -> bool {
    if ari_time.is_some_and(|t| now > t) {
        return true;
    }
    if let Some(before) = renew_before_expiry {
        return not_after < now + before;
    }
    if ari_time.is_none() {
        let lifetime = not_after - not_before;
        let at = if lifetime < 10 * 86_400 {
            not_before + lifetime / 2
        } else {
            not_before + lifetime * 2 / 3
        };
        return now > at;
    }
    false
}

/// What a renewal file asks for, checked before anything is due so a setting
/// this tool can't honour fails every pass rather than on the day it matters.
struct Plan {
    server: String,
    key: KeySpec,
    webroots: HashMap<String, PathBuf>,
    profile: Option<String>,
    required_profile: bool,
    autorenew: bool,
    renew_before_expiry: Option<i64>,
}

impl Plan {
    fn new(lineage: &Lineage, domains: &[String]) -> Result<Self> {
        let conf = &lineage.conf;
        let authenticator = conf.param("authenticator").unwrap_or("none");
        ensure!(
            authenticator == "webroot",
            "authenticator {authenticator} is not supported, only webroot is"
        );
        if let Some(installer) = conf.param("installer") {
            bail!("installer {installer} is not supported");
        }
        for key in ["pre_hook", "post_hook", "renew_hook", "deploy_hook"] {
            ensure!(
                conf.param(key).is_none(),
                "{key} is set, and this tool doesn't run hooks"
            );
        }
        ensure!(
            conf::boolean(conf.param("reuse_key"))? != Some(true),
            "reuse_key is not supported"
        );
        ensure!(
            conf::boolean(conf.param("must_staple"))? != Some(true),
            "must_staple is not supported"
        );
        if let Some(challenges) = conf.param("pref_challs") {
            ensure!(
                conf::list(challenges).iter().any(|c| c.eq_ignore_ascii_case("http-01")),
                "pref_challs {challenges} leaves out http-01"
            );
        }
        if conf.param("preferred_chain").is_some() {
            warning!(
                "{}: ignoring preferred_chain, the CA's default chain is used",
                lineage.name
            );
        }
        let key = KeySpec::from_params(
            conf.param("key_type"),
            conf.param("elliptic_curve"),
            conf.param("rsa_key_size"),
        )?;
        let mut webroots = HashMap::new();
        for domain in domains {
            let webroot = conf
                .webroot_for(domain)
                .ok_or_else(|| anyhow!("no webroot_path or webroot_map entry for {domain}"))?;
            webroots.insert(domain.clone(), PathBuf::from(webroot));
        }
        let (profile, required_profile) = match (conf.param("required_profile"), conf.param("preferred_profile")) {
            (Some(p), _) => (Some(p.to_owned()), true),
            (None, Some(p)) => (Some(p.to_owned()), false),
            (None, None) => (None, false),
        };
        Ok(Plan {
            server: conf.param("server").unwrap_or(crate::LETS_ENCRYPT).to_owned(),
            key,
            webroots,
            profile,
            required_profile,
            autorenew: conf::boolean(conf.param("autorenew"))?.unwrap_or(true),
            renew_before_expiry: conf
                .get("renew_before_expiry")
                .map(conf::interval_seconds)
                .transpose()?,
        })
    }

    /// The profile to ask for: a required one always, a preferred one only
    /// when the server offers it.
    fn profile_for(&self, account: &instant_acme::Account) -> Result<Option<String>> {
        let Some(profile) = &self.profile else { return Ok(None) };
        if self.required_profile || account.profiles().any(|p| p.name == profile) {
            return Ok(Some(profile.clone()));
        }
        Ok(None)
    }
}

fn now() -> i64 {
    time::OffsetDateTime::now_utc().unix_timestamp()
}

/// One pass over `renewal/*.conf`. Returns whether every renewal that was
/// due succeeded.
pub async fn renew_all(settings: &Settings, force: bool, only: &[String]) -> Result<bool> {
    let _lock = lineage::lock(&settings.config_dir)?;
    let mut acme = Acme::new(&settings.config_dir, settings.ca_cert.as_deref())?;
    let mut confs = lineage::renewal_confs(&settings.config_dir)?;
    if !only.is_empty() {
        for name in only {
            ensure!(
                confs.iter().any(|c| c.file_stem().is_some_and(|s| s == name.as_str())),
                "there is no renewal/{name}.conf"
            );
        }
        confs.retain(|c| c.file_stem().is_some_and(|s| only.iter().any(|n| s == n.as_str())));
    }
    if confs.is_empty() {
        info!("no certificates in {}", settings.config_dir.join("renewal").display());
        return Ok(true);
    }
    let (mut renewed, mut not_due, mut failed) = (Vec::new(), Vec::new(), Vec::new());
    for path in &confs {
        let name = path
            .file_stem()
            .map(|s| s.to_string_lossy().into_owned())
            .unwrap_or_default();
        match tokio::time::timeout(LINEAGE_TIMEOUT, renew_one(&mut acme, path, force)).await {
            Ok(Ok(true)) => renewed.push(name),
            Ok(Ok(false)) => not_due.push(name),
            Ok(Err(e)) => {
                error!("{name}: renewal failed: {e:#}");
                failed.push(name);
            }
            Err(_) => {
                error!("{name}: renewal failed: no result after {}s", LINEAGE_TIMEOUT.as_secs());
                failed.push(name);
            }
        }
    }
    info!(
        "renewed {} [{}], not due {}, failed {} [{}]",
        renewed.len(),
        renewed.join(" "),
        not_due.len(),
        failed.len(),
        failed.join(" ")
    );
    Ok(failed.is_empty())
}

async fn renew_one(acme: &mut Acme, conf_path: &Path, force: bool) -> Result<bool> {
    let lineage = Lineage::load(conf_path)?;
    let name = lineage.name.clone();
    let current = lineage.current_version()?;
    lineage.clean_up(current)?;
    let cert = CertInfo::from_pem(&lineage.read_current("cert")?).context("reading the current certificate")?;
    ensure!(
        cert.other_names == 0,
        "the certificate has names other than DNS names, which webroot can't validate"
    );
    ensure!(!cert.dns_names.is_empty(), "the certificate names no domains");
    ensure!(
        !cert.dns_names.iter().any(|d| d.starts_with("*.")),
        "wildcard names need DNS validation, not webroot"
    );
    let plan = Plan::new(&lineage, &cert.dns_names)?;

    if !force {
        if !plan.autorenew {
            info!("{name}: autorenew is off, skipping");
            return Ok(false);
        }
        let ari = match acme.existing(&plan.server).await {
            Ok(Some(account)) => match acme::ari_renewal_time(&account, &cert.der).await {
                Ok(time) => Some(time),
                Err(e) => {
                    warning!(
                        "{name}: no renewal information from the server ({e:#}), using the certificate's lifetime"
                    );
                    None
                }
            },
            Ok(None) => None,
            Err(e) => {
                warning!("{name}: no renewal information ({e:#}), using the certificate's lifetime");
                None
            }
        };
        if !due(now(), cert.not_before, cert.not_after, plan.renew_before_expiry, ari) {
            info!("{name}: not due, expires {}", utc(cert.not_after));
            return Ok(false);
        }
    }

    info!(
        "{name}: renewing {} ({}), expires {}",
        cert.dns_names.join(" "),
        plan.key,
        utc(cert.not_after)
    );
    let account = acme.account(&plan.server).await?;
    let profile = plan.profile_for(&account)?;
    let key = plan.key.generate()?;
    let csr = crate::keys::csr(&key, &cert.dns_names)?;
    let chain = acme::obtain(&account, &cert.dns_names, &plan.webroots, &csr, profile.as_deref()).await?;
    let issued = Issued::check(&chain, &key, &cert.dns_names)?;
    let version = lineage.save(&issued.cert, &issued.chain, &key.serialize_pem(), Some(current))?;
    lineage.activate(version)?;
    lineage.truncate(version);
    info!(
        "{name}: renewed, version {version}, expires {}",
        utc(issued.info.not_after)
    );
    Ok(true)
}

pub struct IssueRequest {
    pub cert_name: String,
    pub domains: Vec<String>,
    pub webroot: PathBuf,
    pub server: String,
    pub key: KeySpec,
}

/// Issues a certificate into a new lineage, in the layout and renewal file
/// certbot would have written, so `renew` (or certbot) keeps it renewed.
pub async fn issue(settings: &Settings, request: &IssueRequest) -> Result<()> {
    let name = &request.cert_name;
    ensure!(
        !name.is_empty() && !name.starts_with('.') && !name.contains('/') && name != "..",
        "{name:?} can't be a certificate name"
    );
    ensure!(!request.domains.is_empty(), "name at least one domain");
    for domain in &request.domains {
        ensure!(
            !domain.starts_with("*."),
            "{domain}: wildcard names need DNS validation, not webroot"
        );
    }
    let _lock = lineage::lock(&settings.config_dir)?;
    let config = &settings.config_dir;
    let live_dir = config.join("live").join(name);
    ensure!(
        fs::symlink_metadata(&live_dir).is_err(),
        "{} already exists",
        live_dir.display()
    );

    let mut acme = Acme::new(config, settings.ca_cert.as_deref())?;
    let account = acme.account(&request.server).await?;
    let key = request.key.generate()?;
    let csr = crate::keys::csr(&key, &request.domains)?;
    let webroots = request
        .domains
        .iter()
        .map(|d| (d.clone(), request.webroot.clone()))
        .collect();
    let chain = acme::obtain(&account, &request.domains, &webroots, &csr, None).await?;
    let issued = Issued::check(&chain, &key, &request.domains)?;

    // The renewal file goes first: if what follows is cut short, renew fails
    // loudly on the missing links rather than the certificate going unrenewed.
    for dir in ["renewal", "archive", "live"] {
        let path = config.join(dir);
        if !path.exists() {
            fs::create_dir_all(&path)?;
            fs::set_permissions(&path, fs::Permissions::from_mode(0o700))?;
        }
    }
    let archive_dir = config.join("archive").join(name);
    let archive = archive_dir.to_string_lossy();
    let links = KINDS.map(|kind| {
        (
            kind,
            live_dir.join(format!("{kind}.pem")).to_string_lossy().into_owned(),
        )
    });
    let webroot = request.webroot.to_string_lossy().into_owned();
    let mut params = Vec::new();
    match acme::certbot_account_ids(config, &request.server).as_slice() {
        [id] => params.push(("account", id.clone())),
        _ => warning!(
            "{name}: no single certbot account for {}, so the renewal file names none",
            request.server
        ),
    }
    params.push(("authenticator", "webroot".to_owned()));
    params.push(("webroot_path", format!("{webroot},")));
    params.push(("server", request.server.clone()));
    params.extend(request.key.params());
    let text = NewLineage {
        archive_dir: &archive,
        links,
        params,
        webroot_map: request.domains.iter().map(|d| (d.clone(), webroot.clone())).collect(),
    }
    .render();
    let conf_path = config.join("renewal").join(format!("{name}.conf"));
    write_atomic(&conf_path, text.as_bytes(), 0o644, None)?;

    let lineage = Lineage::load(&conf_path)?;
    let version = lineage.save(&issued.cert, &issued.chain, &key.serialize_pem(), None)?;
    lineage.activate(version)?;
    info!(
        "{name}: issued for {}, expires {}",
        request.domains.join(" "),
        utc(issued.info.not_after)
    );
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::due;

    const DAY: i64 = 86_400;

    #[test]
    fn ninety_day_certificates_renew_with_thirty_days_left() {
        let (nb, na) = (0, 90 * DAY);
        assert!(!due(59 * DAY, nb, na, None, None));
        assert!(due(60 * DAY + 1, nb, na, None, None));
    }

    #[test]
    fn short_certificates_renew_at_half_life() {
        assert!(!due(2 * DAY, 0, 6 * DAY, None, None));
        assert!(due(3 * DAY + 1, 0, 6 * DAY, None, None));
    }

    #[test]
    fn renew_before_expiry_wins_over_the_lifetime() {
        assert!(due(10 * DAY, 0, 90 * DAY, Some(85 * DAY), None));
        assert!(!due(70 * DAY, 0, 90 * DAY, Some(10 * DAY), None));
    }

    #[test]
    fn ari_decides_when_it_answers() {
        assert!(due(10 * DAY, 0, 90 * DAY, None, Some(5 * DAY)));
        assert!(!due(70 * DAY, 0, 90 * DAY, None, Some(80 * DAY)));
        assert!(due(70 * DAY, 0, 90 * DAY, Some(30 * DAY), Some(80 * DAY)));
    }
}
