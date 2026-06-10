// Sequora wallet — Rust shared-core prototype.
// Generates a post-quantum ML-DSA-65 key, derives the chain's sqr1... address
// (SHA-256(pubkey)[:20] + bech32 "sqr" — identical to the Go chain), and queries
// a balance from the chain's REST API.

use std::env;
use std::fs;
use std::io::Read;
use std::os::unix::fs::{DirBuilderExt, OpenOptionsExt};
use std::path::PathBuf;

use bech32::{ToBase32, Variant};
use fips204::ml_dsa_65;
use fips204::traits::{KeyGen, SerDes, Signer};
use sha2::{Digest, Sha256};
use zeroize::Zeroize;

use argon2::{Algorithm, Argon2, Params, Version};
use base64::Engine;
use chacha20poly1305::aead::Aead;
use chacha20poly1305::{ChaCha20Poly1305, KeyInit, Nonce};
use cosmos_sdk_proto::cosmos::bank::v1beta1::MsgSend;
use cosmos_sdk_proto::cosmos::base::v1beta1::Coin;
use cosmos_sdk_proto::cosmos::distribution::v1beta1::{
    MsgWithdrawDelegatorReward, MsgWithdrawValidatorCommission,
};
use cosmos_sdk_proto::cosmos::slashing::v1beta1::MsgUnjail;
use cosmos_sdk_proto::cosmos::staking::v1beta1::{MsgDelegate, MsgUndelegate};
use cosmos_sdk_proto::cosmos::tx::signing::v1beta1::SignMode;
use cosmos_sdk_proto::cosmos::tx::v1beta1::{
    mode_info, AuthInfo, Fee, ModeInfo, SignDoc, SignerInfo, TxBody, TxRaw,
};
use cosmos_sdk_proto::Any;
use prost::Message;

const HRP: &str = "sqr";
const DENOM: &str = "usqr";

fn key_path() -> PathBuf {
    let home = env::var("HOME").unwrap_or_else(|_| ".".into());
    PathBuf::from(home).join(".sequora-wallet").join("key.json")
}

// --- key-at-rest encryption (Argon2id KDF + ChaCha20-Poly1305 AEAD) ---

fn get_password() -> String {
    // Prefer the env var for scripted/CI use; otherwise prompt with no echo so the
    // password isn't exposed in process env / shell history. (threat-model: env-var
    // password leak). A production build would also support the OS keychain.
    match env::var("SQRWALLET_PASSWORD") {
        Ok(p) => p,
        Err(_) => rpassword::prompt_password("Wallet password: ").expect("failed to read password"),
    }
}

fn rand_bytes(n: usize) -> Vec<u8> {
    let mut b = vec![0u8; n];
    getrandom::getrandom(&mut b).expect("rng");
    b
}

// Hardened Argon2id parameters for NEW wallets (recorded in the key file so they
// can be upgraded later). 64 MiB memory, 3 iterations, 1 lane — well above the
// library default (~19 MiB / t=2), making offline cracking of an exfiltrated
// key.json far more expensive. See SECURITY findings (H3).
const ARGON2_M_COST: u32 = 65536; // KiB = 64 MiB
const ARGON2_T_COST: u32 = 3;
const ARGON2_P_COST: u32 = 1;
// The library defaults, used as a fallback for wallets created before params
// were recorded in the file (keeps older key.json files decryptable).
const ARGON2_DEFAULT_M: u32 = 19456;
const ARGON2_DEFAULT_T: u32 = 2;
const ARGON2_DEFAULT_P: u32 = 1;

fn derive_key(password: &str, salt: &[u8], m: u32, t: u32, p: u32) -> [u8; 32] {
    let mut key = [0u8; 32];
    let params = Params::new(m, t, p, Some(32)).expect("argon2 params");
    Argon2::new(Algorithm::Argon2id, Version::V0x13, params)
        .hash_password_into(password.as_bytes(), salt, &mut key)
        .expect("argon2id");
    key
}

// derive_address matches the chain: bech32("sqr", SHA256(pubkey)[:20]).
fn derive_address(pubkey: &[u8]) -> String {
    let hash = Sha256::digest(pubkey);
    let addr20: [u8; 20] = hash[..20].try_into().unwrap();
    bech32::encode(HRP, addr20.to_base32(), Variant::Bech32).expect("bech32 encode")
}

// derive_valoper is the validator-operator address for THIS wallet: the same
// 20-byte account hash, bech32-encoded with the "sqrvaloper" prefix (Cosmos
// convention). It lets the wallet recognize a validator it operates.
fn derive_valoper(pubkey: &[u8]) -> String {
    let hash = Sha256::digest(pubkey);
    let addr20: [u8; 20] = hash[..20].try_into().unwrap();
    bech32::encode("sqrvaloper", addr20.to_base32(), Variant::Bech32).expect("bech32 encode")
}

fn load_pubkey() -> Vec<u8> {
    let data = fs::read_to_string(key_path()).expect("no wallet found — run `sqrwallet new` first");
    let v: serde_json::Value = serde_json::from_str(&data).expect("corrupt key file");
    hex::decode(v["pubkey"].as_str().expect("missing pubkey")).expect("bad hex")
}

// Derive the keypair from a 32-byte seed, encrypt the SEED at rest, and write
// key.json (0600). The seed is all that's needed to regenerate the key — it is
// exactly what the 24-word recovery phrase encodes. Returns the sqr1 address.
fn save_wallet_from_seed(seed: &[u8; 32], password: &str) -> Result<String, String> {
    let (pk, _sk) = ml_dsa_65::KG::keygen_from_seed(seed);
    let pk_bytes = pk.into_bytes();
    let addr = derive_address(&pk_bytes);

    // Never silently destroy an existing wallet: if key.json is present, back it
    // up (0600 perms are preserved by the copy) before overwriting. A mistaken
    // `new`/restore is then recoverable. (audit: destructive /api/restore)
    if key_path().exists() {
        // Back up the existing key to a UNIQUE timestamped file BEFORE overwriting,
        // and ABORT if the backup fails — never destroy the only copy of a funded
        // key on a best-effort copy. (audit MED: destructive restore/new)
        let ts = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_secs())
            .unwrap_or(0);
        let bak = key_path().with_extension(format!("json.{}.bak", ts));
        if let Err(e) = fs::copy(key_path(), &bak) {
            return Err(format!("refusing to overwrite existing wallet: backup to {} failed: {}", bak.display(), e));
        }
    }

    let salt = rand_bytes(16);
    let nonce = rand_bytes(12);
    let mut key = derive_key(password, &salt, ARGON2_M_COST, ARGON2_T_COST, ARGON2_P_COST);
    let cipher = ChaCha20Poly1305::new_from_slice(&key).expect("cipher");
    let mut seed_vec = seed.to_vec();
    let ciphertext = cipher
        .encrypt(Nonce::from_slice(&nonce), seed_vec.as_ref())
        .expect("encrypt");
    key.zeroize(); // scrub the derived key
    seed_vec.zeroize(); // scrub the plaintext seed buffer

    let dir = key_path().parent().unwrap().to_path_buf();
    // dir 0700: only the owner may traverse ~/.sequora-wallet
    fs::DirBuilder::new().recursive(true).mode(0o700).create(&dir).unwrap();
    let json = serde_json::json!({
        "scheme": "ML-DSA-65",
        "pubkey": hex::encode(&pk_bytes),
        "address": addr,
        "enc": {
            "kdf": "argon2id",
            "cipher": "chacha20poly1305",
            "m_cost": ARGON2_M_COST,
            "t_cost": ARGON2_T_COST,
            "p_cost": ARGON2_P_COST,
            "salt": hex::encode(&salt),
            "nonce": hex::encode(&nonce),
            "seed_ciphertext": hex::encode(&ciphertext),
        }
    });
    // file 0600 from creation (no world-readable TOCTOU window). See finding H2.
    let mut f = fs::OpenOptions::new()
        .write(true)
        .create(true)
        .truncate(true)
        .mode(0o600)
        .open(key_path())
        .unwrap();
    use std::io::Write as _;
    f.write_all(serde_json::to_string_pretty(&json).unwrap().as_bytes()).unwrap();
    Ok(addr)
}

fn cmd_new() {
    let password = get_password();
    // 32 bytes of entropy = the FIPS-204 seed AND the 24-word recovery phrase.
    let mut entropy = rand_bytes(32);
    let mnemonic = bip39::Mnemonic::from_entropy(&entropy).expect("mnemonic");
    let mut seed = [0u8; 32];
    seed.copy_from_slice(&entropy);
    let res = save_wallet_from_seed(&seed, &password);
    seed.zeroize();
    entropy.zeroize();
    let addr = res.expect("failed to save wallet");

    println!("New ENCRYPTED Sequora wallet (post-quantum, ML-DSA-65 / FIPS 204)");
    println!();
    println!("  ┌─ RECOVERY PHRASE (24 words) — WRITE THIS DOWN ON PAPER ─────────");
    println!("  │  {}", mnemonic);
    println!("  └─ Anyone with these words controls your funds. Store offline only:");
    println!("     no photo, no cloud, no text file. This is the ONLY way to recover");
    println!("     your wallet if this computer is lost.");
    println!();
    println!("  address     : {}", addr);
    println!("  key at rest : Argon2id + ChaCha20-Poly1305 (seed encrypted; key never stored in plaintext)");
    println!("  saved to    : {}", key_path().display());
    println!("  restore     : sqrwallet restore   (with SQRWALLET_MNEMONIC + SQRWALLET_PASSWORD set)");
}

fn cmd_restore() {
    let password = get_password();
    let mut phrase = env::var("SQRWALLET_MNEMONIC")
        .expect("set SQRWALLET_MNEMONIC to your 24-word recovery phrase (and SQRWALLET_PASSWORD to a new password)");
    let mnemonic = bip39::Mnemonic::parse(phrase.trim())
        .expect("invalid recovery phrase — check the words and their order");
    let mut entropy = mnemonic.to_entropy();
    if entropy.len() != 32 {
        panic!("expected a 24-word recovery phrase");
    }
    let mut seed = [0u8; 32];
    seed.copy_from_slice(&entropy);
    let res = save_wallet_from_seed(&seed, &password);
    seed.zeroize();
    entropy.zeroize(); // scrub the raw 32-byte master secret
    phrase.zeroize();  // scrub the recovery phrase string
    let addr = res.expect("failed to save wallet");

    println!("Wallet restored from recovery phrase.");
    println!("  address  : {}", addr);
    println!("  saved to : {}", key_path().display());
}

fn cmd_address() {
    println!("{}", derive_address(&load_pubkey()));
}

// cmd_sign signs a message with the wallet's ML-DSA-65 key and prints the
// pubkey/message/signature as hex — so the chain (MsgVerifyPqc) can verify it,
// proving Rust(fips204) <-> Go(circl) signature interop.
fn cmd_sign(message: &str) {
    let (pubkey, sk) = load_keypair(&get_password()); // decrypts with SQRWALLET_PASSWORD
    let sig = sk.try_sign(message.as_bytes(), &[]).expect("sign"); // empty context
    println!("PUBKEY={}", hex::encode(&pubkey));
    println!("MESSAGE={}", message);
    println!("SIG={}", hex::encode(sig));
}

fn cmd_balance(rest: &str) {
    let addr = derive_address(&load_pubkey());
    let url = format!(
        "{}/cosmos/bank/v1beta1/balances/{}",
        rest.trim_end_matches('/'),
        addr
    );
    println!("address: {}", addr);
    match ureq::get(&url).timeout(std::time::Duration::from_secs(15)).call() {
        Ok(r) => {
            let body = r.into_string().unwrap_or_default();
            let v: serde_json::Value = serde_json::from_str(&body).unwrap_or(serde_json::json!({}));
            let empty = vec![];
            let balances = v["balances"].as_array().unwrap_or(&empty);
            if balances.is_empty() {
                println!("balance: 0 {}", DENOM);
            } else {
                for b in balances {
                    let amt = b["amount"].as_str().unwrap_or("?");
                    let den = b["denom"].as_str().unwrap_or("?");
                    let sqr = amt.parse::<f64>().unwrap_or(0.0) / 1_000_000.0;
                    println!("balance: {} {}  ({} SQR)", amt, den, sqr);
                }
            }
        }
        Err(e) => println!("query failed: {e}\n(is the chain REST API up at {rest}?)"),
    }
}

fn load_keypair(pw: &str) -> (Vec<u8>, ml_dsa_65::PrivateKey) {
    let data = fs::read_to_string(key_path()).expect("no wallet — run `sqrwallet new`");
    let v: serde_json::Value = serde_json::from_str(&data).expect("corrupt key file");
    let pubkey = hex::decode(v["pubkey"].as_str().unwrap()).unwrap();
    let enc = &v["enc"];
    let salt = hex::decode(enc["salt"].as_str().expect("salt")).unwrap();
    let nonce = hex::decode(enc["nonce"].as_str().expect("nonce")).unwrap();
    // Use the params recorded in the file; fall back to the library defaults for
    // wallets created before params were stored (keeps old key.json decryptable).
    let m = enc["m_cost"].as_u64().map(|v| v as u32).unwrap_or(ARGON2_DEFAULT_M);
    let t = enc["t_cost"].as_u64().map(|v| v as u32).unwrap_or(ARGON2_DEFAULT_T);
    let p = enc["p_cost"].as_u64().map(|v| v as u32).unwrap_or(ARGON2_DEFAULT_P);
    let mut key = derive_key(pw, &salt, m, t, p);
    let cipher = ChaCha20Poly1305::new_from_slice(&key).expect("cipher");

    let sk = if let Some(seed_ct) = enc["seed_ciphertext"].as_str() {
        // New seed-based wallet (has a recovery phrase): decrypt the 32-byte seed
        // and re-derive the key deterministically.
        let ct = hex::decode(seed_ct).unwrap();
        let mut seed_vec = cipher
            .decrypt(Nonce::from_slice(&nonce), ct.as_ref())
            .expect("decrypt failed — wrong password?");
        let mut seed = [0u8; 32];
        seed.copy_from_slice(&seed_vec);
        seed_vec.zeroize();
        let (pk2, sk) = ml_dsa_65::KG::keygen_from_seed(&seed);
        seed.zeroize();
        // Integrity: pubkey/address live OUTSIDE the AEAD, so verify the decrypted
        // seed actually derives the stored pubkey; reject a tampered file. (audit LOW)
        let pk2b = pk2.into_bytes();
        if &pk2b[..] != &pubkey[..] {
            panic!("key file integrity check failed: stored pubkey does not match the decrypted seed");
        }
        sk
    } else {
        // Legacy wallet: the private key itself is encrypted (no recovery phrase).
        let ct = hex::decode(enc["ciphertext"].as_str().expect("ciphertext")).unwrap();
        let mut sk_vec = cipher
            .decrypt(Nonce::from_slice(&nonce), ct.as_ref())
            .expect("decrypt failed — wrong password?");
        let mut sk_arr: [u8; ml_dsa_65::SK_LEN] = sk_vec.as_slice().try_into().expect("bad privkey length");
        sk_vec.zeroize();
        let sk = ml_dsa_65::PrivateKey::try_from_bytes(sk_arr).expect("load privkey");
        sk_arr.zeroize();
        sk
    };
    key.zeroize(); // scrub the derived key
    (pubkey, sk)
}

// proto-encode the custom pubkey message { bytes key = 1 } (the Any's value).
fn pubkey_any_value(pk: &[u8]) -> Vec<u8> {
    let mut v = Vec::with_capacity(pk.len() + 6);
    v.push(0x0a); // field 1, wire type 2
    let mut len = pk.len();
    loop {
        let mut b = (len & 0x7f) as u8;
        len >>= 7;
        if len != 0 {
            b |= 0x80;
        }
        v.push(b);
        if len == 0 {
            break;
        }
    }
    v.extend_from_slice(pk);
    v
}

fn query_account(rest: &str, addr: &str) -> (u64, u64) {
    let url = format!(
        "{}/cosmos/auth/v1beta1/accounts/{}",
        rest.trim_end_matches('/'),
        addr
    );
    let body = ureq::get(&url)
        .timeout(std::time::Duration::from_secs(15))
        .call()
        .expect("account query failed (is it funded?)")
        .into_string()
        .unwrap();
    let v: serde_json::Value = serde_json::from_str(&body).unwrap();
    let acc = &v["account"];
    let an = acc["account_number"].as_str().unwrap_or("0").parse().unwrap_or(0);
    let sq = acc["sequence"].as_str().unwrap_or("0").parse().unwrap_or(0);
    (an, sq)
}

// CLI helper: build+sign+broadcast and print the result (uses SQRWALLET_PASSWORD).
fn sign_and_broadcast(rest: &str, chain_id: &str, msg: Any, gas: u64, fee_usqr: u64) {
    match broadcast_msg(rest, chain_id, msg, gas, fee_usqr, &get_password()) {
        Ok((code, txhash, log)) => {
            println!("  broadcast code={code} txhash={txhash}");
            if !log.is_empty() {
                println!("  raw_log: {log}");
            }
        }
        Err(e) => println!("  error: {e}"),
    }
}

// Builds a SIGN_MODE_DIRECT tx around `msg`, signs the SignDoc with ML-DSA-65,
// broadcasts via REST, and returns (code, txhash, raw_log).
fn broadcast_msg(rest: &str, chain_id: &str, msg: Any, gas: u64, fee_usqr: u64, pw: &str) -> Result<(i64, String, String), String> {
    let (pubkey, sk) = load_keypair(pw);
    let from = derive_address(&pubkey);
    let (acct_num, seq) = query_account(rest, &from);

    let body = TxBody {
        messages: vec![msg],
        memo: String::new(),
        ..Default::default()
    };
    let body_bytes = body.encode_to_vec();

    let pk_any = Any {
        type_url: "/sequora.crypto.v1.PubKey".to_string(),
        value: pubkey_any_value(&pubkey),
    };
    let signer_info = SignerInfo {
        public_key: Some(pk_any),
        mode_info: Some(ModeInfo {
            sum: Some(mode_info::Sum::Single(mode_info::Single {
                mode: SignMode::Direct as i32,
            })),
        }),
        sequence: seq,
    };
    let auth_info = AuthInfo {
        signer_infos: vec![signer_info],
        fee: Some(Fee {
            amount: vec![Coin {
                denom: "usqr".into(),
                amount: fee_usqr.to_string(),
            }],
            gas_limit: gas,
            payer: String::new(),
            granter: String::new(),
        }),
        ..Default::default()
    };
    let auth_info_bytes = auth_info.encode_to_vec();

    let sign_doc = SignDoc {
        body_bytes: body_bytes.clone(),
        auth_info_bytes: auth_info_bytes.clone(),
        chain_id: chain_id.to_string(),
        account_number: acct_num,
    };
    let sig = sk
        .try_sign(&sign_doc.encode_to_vec(), &[])
        .map_err(|e| format!("sign: {e:?}"))?;

    let tx_raw = TxRaw {
        body_bytes,
        auth_info_bytes,
        signatures: vec![sig.to_vec()],
    };
    let tx_b64 = base64::engine::general_purpose::STANDARD.encode(tx_raw.encode_to_vec());

    let url = format!("{}/cosmos/tx/v1beta1/txs", rest.trim_end_matches('/'));
    let resp = ureq::post(&url)
        .timeout(std::time::Duration::from_secs(20))
        .send_json(serde_json::json!({"tx_bytes": tx_b64, "mode": "BROADCAST_MODE_SYNC"}))
        .map_err(|e| format!("broadcast: {e}"))?;
    let v: serde_json::Value =
        serde_json::from_str(&resp.into_string().unwrap_or_default()).map_err(|e| e.to_string())?;
    let tr = &v["tx_response"];
    Ok((
        tr["code"].as_i64().unwrap_or(-1),
        tr["txhash"].as_str().unwrap_or("").to_string(),
        tr["raw_log"].as_str().unwrap_or("").to_string(),
    ))
}

fn my_address() -> String {
    derive_address(&load_pubkey()) // no password needed (pubkey is public)
}

fn cmd_stake(rest: &str, chain_id: &str, valoper: &str, amount: &str) {
    let msg = MsgDelegate {
        delegator_address: my_address(),
        validator_address: valoper.to_string(),
        amount: Some(Coin { denom: "usqr".into(), amount: amount.to_string() }),
    };
    let any = Any {
        type_url: "/cosmos.staking.v1beta1.MsgDelegate".to_string(),
        value: msg.encode_to_vec(),
    };
    println!("ONE-TAP STAKE: delegating {amount} usqr -> {valoper}");
    sign_and_broadcast(rest, chain_id, any, 500_000, 15_000);
}

fn cmd_send(rest: &str, chain_id: &str, to: &str, amount: &str) {
    let msg = MsgSend {
        from_address: my_address(),
        to_address: to.to_string(),
        amount: vec![Coin { denom: "usqr".into(), amount: amount.to_string() }],
    };
    let any = Any {
        type_url: "/cosmos.bank.v1beta1.MsgSend".to_string(),
        value: msg.encode_to_vec(),
    };
    println!("SEND: {amount} usqr -> {to}");
    // PQC txs need more gas: the 1952-byte pubkey is written + ML-DSA verify (10x).
    sign_and_broadcast(rest, chain_id, any, 400_000, 12_000);
}

fn cmd_claim(rest: &str, chain_id: &str, valoper: &str) {
    let msg = MsgWithdrawDelegatorReward {
        delegator_address: my_address(),
        validator_address: valoper.to_string(),
    };
    let any = Any {
        type_url: "/cosmos.distribution.v1beta1.MsgWithdrawDelegatorReward".to_string(),
        value: msg.encode_to_vec(),
    };
    println!("CLAIM staking rewards from {valoper}");
    sign_and_broadcast(rest, chain_id, any, 300_000, 9_000);
}

fn cmd_unstake(rest: &str, chain_id: &str, valoper: &str, amount: &str) {
    let msg = MsgUndelegate {
        delegator_address: my_address(),
        validator_address: valoper.to_string(),
        amount: Some(Coin { denom: "usqr".into(), amount: amount.to_string() }),
    };
    let any = Any {
        type_url: "/cosmos.staking.v1beta1.MsgUndelegate".to_string(),
        value: msg.encode_to_vec(),
    };
    println!("UNSTAKE: undelegating {amount} usqr from {valoper}");
    sign_and_broadcast(rest, chain_id, any, 500_000, 15_000);
}

// ---------------- web wallet UI (local HTTP server) ----------------

fn rest_get(rest: &str, path: &str) -> serde_json::Value {
    let url = format!("{}{}", rest.trim_end_matches('/'), path);
    match ureq::get(&url).timeout(std::time::Duration::from_secs(15)).call() {
        Ok(r) => serde_json::from_str(&r.into_string().unwrap_or_default()).unwrap_or(serde_json::json!({})),
        Err(_) => serde_json::json!({}),
    }
}

fn info_json(rest: &str) -> String {
    let addr = derive_address(&load_pubkey());
    let bal = rest_get(rest, &format!("/cosmos/bank/v1beta1/balances/{addr}"));
    let balance = bal["balances"]
        .as_array()
        .and_then(|a| a.iter().find(|c| c["denom"] == "usqr"))
        .and_then(|c| c["amount"].as_str())
        .unwrap_or("0")
        .to_string();
    let myvaloper = derive_valoper(&load_pubkey());
    let vals = rest_get(rest, "/cosmos/staking/v1beta1/validators?pagination.limit=200");
    let val_arr = vals["validators"].as_array().cloned().unwrap_or_default();
    let validators: Vec<serde_json::Value> = val_arr
        .iter()
        .map(|v| serde_json::json!({
            "moniker": v["description"]["moniker"],
            "valoper": v["operator_address"],
            "tokens": v["tokens"],
            "jailed": v["jailed"],
            "status": v["status"],
            "commission": v["commission"]["commission_rates"]["rate"],
        }))
        .collect();
    // Is THIS wallet operating a validator? (operator address == our valoper)
    let myvalidator = match val_arr.iter().find(|v| v["operator_address"].as_str() == Some(myvaloper.as_str())) {
        Some(v) => serde_json::json!({
            "exists": true,
            "moniker": v["description"]["moniker"],
            "tokens": v["tokens"],
            "jailed": v["jailed"],
            "status": v["status"],
            "commission": v["commission"]["commission_rates"]["rate"],
        }),
        None => serde_json::json!({"exists": false}),
    };
    let dels = rest_get(rest, &format!("/cosmos/staking/v1beta1/delegations/{addr}"));
    let delegations: Vec<serde_json::Value> = dels["delegation_responses"]
        .as_array()
        .cloned()
        .unwrap_or_default()
        .iter()
        .map(|d| serde_json::json!({"valoper": d["delegation"]["validator_address"], "amount": d["balance"]["amount"]}))
        .collect();
    let rew = rest_get(rest, &format!("/cosmos/distribution/v1beta1/delegators/{addr}/rewards"));
    let rewards = rew["total"]
        .as_array()
        .and_then(|a| a.iter().find(|c| c["denom"] == "usqr"))
        .and_then(|c| c["amount"].as_str())
        .map(|s| s.split('.').next().unwrap_or("0").to_string())
        .unwrap_or_else(|| "0".into());
    serde_json::json!({"address": addr, "balance": balance, "rewards": rewards, "validators": validators, "delegations": delegations, "myvaloper": myvaloper, "myvalidator": myvalidator}).to_string()
}

fn api_action(body: &str, rest: &str, chain_id: &str, kind: &str) -> (u16, &'static str, String) {
    let v: serde_json::Value = serde_json::from_str(body).unwrap_or(serde_json::json!({}));
    let pw = v["password"].as_str().unwrap_or("").to_string();
    let from = derive_address(&load_pubkey());
    let (any, gas, fee): (Any, u64, u64) = match kind {
        "send" => {
            let msg = MsgSend {
                from_address: from,
                to_address: v["to"].as_str().unwrap_or("").to_string(),
                amount: vec![Coin { denom: "usqr".into(), amount: v["amount"].as_str().unwrap_or("0").to_string() }],
            };
            (Any { type_url: "/cosmos.bank.v1beta1.MsgSend".into(), value: msg.encode_to_vec() }, 400_000, 12_000)
        }
        "stake" => {
            let msg = MsgDelegate {
                delegator_address: from,
                validator_address: v["valoper"].as_str().unwrap_or("").to_string(),
                amount: Some(Coin { denom: "usqr".into(), amount: v["amount"].as_str().unwrap_or("0").to_string() }),
            };
            (Any { type_url: "/cosmos.staking.v1beta1.MsgDelegate".into(), value: msg.encode_to_vec() }, 500_000, 15_000)
        }
        "claim" => {
            let msg = MsgWithdrawDelegatorReward {
                delegator_address: from,
                validator_address: v["valoper"].as_str().unwrap_or("").to_string(),
            };
            (Any { type_url: "/cosmos.distribution.v1beta1.MsgWithdrawDelegatorReward".into(), value: msg.encode_to_vec() }, 300_000, 9_000)
        }
        "unjail" => {
            // Operator action: free your own validator after a downtime jail.
            let msg = MsgUnjail { validator_addr: derive_valoper(&load_pubkey()) };
            (Any { type_url: "/cosmos.slashing.v1beta1.MsgUnjail".into(), value: msg.encode_to_vec() }, 200_000, 6_000)
        }
        "withdrawcommission" => {
            // Operator action: withdraw the commission your validator has earned.
            let msg = MsgWithdrawValidatorCommission { validator_address: derive_valoper(&load_pubkey()) };
            (Any { type_url: "/cosmos.distribution.v1beta1.MsgWithdrawValidatorCommission".into(), value: msg.encode_to_vec() }, 300_000, 9_000)
        }
        _ => return (400, "application/json", "{\"error\":\"unknown action\"}".into()),
    };
    match broadcast_msg(rest, chain_id, any, gas, fee, &pw) {
        Ok((code, txhash, log)) => (200, "application/json", serde_json::json!({"code": code, "txhash": txhash, "log": log}).to_string()),
        Err(e) => (200, "application/json", serde_json::json!({"error": e}).to_string()),
    }
}

// verify_password checks that `pw` decrypts the key, WITHOUT retaining anything:
// it decrypts, immediately drops (load_keypair zeroizes its buffers), and reports
// only ok/fail. Used by the lock screen so the user gets "wrong password" feedback
// at unlock time. The decrypted key is never held between requests.
fn verify_password(pw: &str) -> bool {
    // The quiet panic hook is installed ONCE at server startup (see cmd_serve).
    // We must NOT mutate the global hook per-request — that raced across the 8
    // worker threads. Here we only catch the expected wrong-password panic.
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _ = load_keypair(pw);
    }))
    .is_ok()
}

fn api_unlock(body: &str) -> (u16, &'static str, String) {
    let v: serde_json::Value = serde_json::from_str(body).unwrap_or(serde_json::json!({}));
    let pw = v["password"].as_str().unwrap_or("");
    if pw.is_empty() {
        return (200, "application/json", "{\"ok\":false,\"error\":\"enter your password\"}".into());
    }
    if verify_password(pw) {
        (200, "application/json", "{\"ok\":true}".into())
    } else {
        (200, "application/json", "{\"ok\":false,\"error\":\"wrong password\"}".into())
    }
}

// Recover a wallet from a 24-word phrase. Re-derives the key from the seed and
// writes a fresh key.json encrypted under the supplied (new) password.
fn api_restore(body: &str) -> (u16, &'static str, String) {
    let v: serde_json::Value = serde_json::from_str(body).unwrap_or(serde_json::json!({}));
    let mut phrase = v["mnemonic"].as_str().unwrap_or("").trim().to_string();
    let pw = v["password"].as_str().unwrap_or("");
    if phrase.is_empty() || pw.is_empty() {
        return (200, "application/json", "{\"ok\":false,\"error\":\"recovery phrase and a new password are both required\"}".into());
    }
    let mnemonic = match bip39::Mnemonic::parse(&phrase) {
        Ok(m) => m,
        Err(_) => return (200, "application/json", "{\"ok\":false,\"error\":\"invalid recovery phrase — check the words and order\"}".into()),
    };
    let mut entropy = mnemonic.to_entropy();
    if entropy.len() != 32 {
        return (200, "application/json", "{\"ok\":false,\"error\":\"expected a 24-word recovery phrase\"}".into());
    }
    let mut seed = [0u8; 32];
    seed.copy_from_slice(&entropy);
    let res = save_wallet_from_seed(&seed, pw);
    seed.zeroize();
    entropy.zeroize(); // scrub raw master secret
    phrase.zeroize();  // scrub the supplied recovery phrase
    match res {
        Ok(addr) => (200, "application/json", serde_json::json!({"ok": true, "address": addr}).to_string()),
        Err(e) => (200, "application/json", serde_json::json!({"ok": false, "error": e}).to_string()),
    }
}

// Create a brand-new wallet: generate fresh 32-byte entropy -> 24-word phrase ->
// ML-DSA keys, write an encrypted key.json under the supplied password, and return
// the address + the phrase ONCE so the user can write it down. (web "create wallet")
fn api_new(body: &str) -> (u16, &'static str, String) {
    let v: serde_json::Value = serde_json::from_str(body).unwrap_or(serde_json::json!({}));
    let pw = v["password"].as_str().unwrap_or("");
    if pw.is_empty() {
        return (200, "application/json", "{\"ok\":false,\"error\":\"a password is required\"}".into());
    }
    let mut entropy = rand_bytes(32);
    let mnemonic = match bip39::Mnemonic::from_entropy(&entropy) {
        Ok(m) => m,
        Err(_) => {
            entropy.zeroize();
            return (200, "application/json", "{\"ok\":false,\"error\":\"key generation failed\"}".into());
        }
    };
    let phrase = mnemonic.to_string();
    let mut seed = [0u8; 32];
    seed.copy_from_slice(&entropy);
    let res = save_wallet_from_seed(&seed, pw);
    seed.zeroize();
    entropy.zeroize();
    match res {
        // phrase is intentionally returned (shown once for the user to record offline);
        // the mnemonic object is zeroized on drop (bip39 zeroize feature).
        Ok(addr) => (200, "application/json", serde_json::json!({"ok": true, "address": addr, "mnemonic": phrase}).to_string()),
        Err(e) => (200, "application/json", serde_json::json!({"ok": false, "error": e}).to_string()),
    }
}

fn route(method: &tiny_http::Method, url: &str, body: &str, chain_id: &str, rest: &str) -> (u16, &'static str, String) {
    match (method, url) {
        (tiny_http::Method::Get, "/") => (200, "text/html", DASHBOARD_HTML.to_string()),
        (tiny_http::Method::Get, "/api/info") => (200, "application/json", info_json(rest)),
        (tiny_http::Method::Post, "/api/unlock") => api_unlock(body),
        (tiny_http::Method::Post, "/api/new") => api_new(body),
        (tiny_http::Method::Post, "/api/restore") => api_restore(body),
        (tiny_http::Method::Post, "/api/send") => api_action(body, rest, chain_id, "send"),
        (tiny_http::Method::Post, "/api/stake") => api_action(body, rest, chain_id, "stake"),
        (tiny_http::Method::Post, "/api/claim") => api_action(body, rest, chain_id, "claim"),
        (tiny_http::Method::Post, "/api/unjail") => api_action(body, rest, chain_id, "unjail"),
        (tiny_http::Method::Post, "/api/withdraw-commission") => api_action(body, rest, chain_id, "withdrawcommission"),
        _ => (404, "text/plain", "not found".into()),
    }
}

// constant-time-ish comparison so the token check isn't a timing oracle.
fn ct_eq(a: &str, b: &str) -> bool {
    let (a, b) = (a.as_bytes(), b.as_bytes());
    if a.len() != b.len() {
        return false;
    }
    let mut diff = 0u8;
    for i in 0..a.len() {
        diff |= a[i] ^ b[i];
    }
    diff == 0
}

fn header_value<'a>(req: &'a tiny_http::Request, name: &str) -> Option<String> {
    req.headers()
        .iter()
        .find(|h| h.field.as_str().as_str().eq_ignore_ascii_case(name))
        .map(|h| h.value.as_str().to_string())
}

// The CSRF token is persisted (0600) so server restarts/reboots don't invalidate
// an already-open wallet page. It stays unguessable and is never readable by a
// remote site (it lives on disk + is embedded only in the same-origin page), so
// persisting it doesn't weaken the CSRF defense — it just makes the UI reliable.
fn session_token_path() -> PathBuf {
    key_path().parent().map(|d| d.join(".session_token")).unwrap_or_else(|| PathBuf::from(".session_token"))
}

fn load_or_create_token() -> String {
    let p = session_token_path();
    if let Ok(s) = fs::read_to_string(&p) {
        let s = s.trim().to_string();
        if s.len() == 64 && s.chars().all(|c| c.is_ascii_hexdigit()) {
            return s;
        }
    }
    let tok = hex::encode(rand_bytes(32));
    if let Some(dir) = p.parent() {
        let _ = fs::DirBuilder::new().recursive(true).mode(0o700).create(dir);
    }
    if let Ok(mut f) = fs::OpenOptions::new().write(true).create(true).truncate(true).mode(0o600).open(&p) {
        use std::io::Write as _;
        let _ = f.write_all(tok.as_bytes());
    }
    tok
}

fn cmd_serve(port: u16, chain_id: &str, rest: &str) {
    let bind = format!("127.0.0.1:{port}"); // localhost only — never expose the signing API to the LAN
    let server = std::sync::Arc::new(tiny_http::Server::http(&bind).expect("bind"));

    // CSRF/auth defense (SECURITY finding C1): a token is embedded into the served
    // page and required on EVERY /api/* request via the X-Sequora-Token header. A
    // malicious site the user visits cannot read this page (same-origin policy) so
    // it cannot learn the token, and the custom header forces a CORS preflight that
    // a cross-origin caller fails. Without this, any website could POST a signed
    // transaction to localhost. Persisted across restarts (see load_or_create_token).
    let token = std::sync::Arc::new(load_or_create_token());
    let allowed_origins = std::sync::Arc::new(vec![
        format!("http://localhost:{port}"),
        format!("http://127.0.0.1:{port}"),
    ]);
    let chain_id = chain_id.to_string();
    let rest = rest.to_string();

    println!("Sequora wallet UI running:");
    println!("  open  http://localhost:{port}  in your browser");
    println!("  chain {chain_id} via {rest}");

    // Install a quiet panic hook ONCE before spawning workers (each request is
    // wrapped in catch_unwind). Avoids per-request global-hook mutation racing
    // across worker threads. (audit: panic-hook race)
    std::panic::set_hook(Box::new(|_| {}));

    // Worker pool: handle requests concurrently so one slow chain-REST round-trip
    // (or a slowloris client) can't block the whole UI. (SECURITY findings M3/M4.)
    let workers = 8;
    let mut handles = Vec::new();
    for _ in 0..workers {
        let server = server.clone();
        let token = token.clone();
        let allowed = allowed_origins.clone();
        let chain_id = chain_id.clone();
        let rest = rest.clone();
        handles.push(std::thread::spawn(move || loop {
            match server.recv() {
                Ok(req) => handle_request(req, &token, &allowed, &chain_id, &rest),
                Err(_) => break,
            }
        }));
    }
    for h in handles {
        let _ = h.join();
    }
}

// Cap request bodies so a slowloris / oversized-body client can't tie up a worker
// or exhaust memory. (SECURITY finding M4.)
const MAX_BODY: u64 = 64 * 1024;

// handle_request processes ONE request on a worker thread: auth (token + origin
// for /api/*), size-capped body read, routing, and the security headers.
fn handle_request(mut req: tiny_http::Request, token: &str, allowed_origins: &[String], chain_id: &str, rest: &str) {
    let method = req.method().clone();
    let url = req.url().to_string();
    let is_api = url.starts_with("/api/");
    if is_api {
        let tok_ok = header_value(&req, "X-Sequora-Token").map(|t| ct_eq(&t, token)).unwrap_or(false);
        let origin_ok = match header_value(&req, "Origin") {
            Some(o) => allowed_origins.iter().any(|a| ct_eq(a, &o)),
            None => true, // same-origin GETs/POSTs may omit Origin
        };
        if !tok_ok || !origin_ok {
            let h = tiny_http::Header::from_bytes(&b"Content-Type"[..], &b"application/json"[..]).unwrap();
            let _ = req.respond(
                tiny_http::Response::from_string("{\"error\":\"forbidden\"}").with_status_code(403).with_header(h),
            );
            return;
        }
    }
    let mut body = String::new();
    if method == tiny_http::Method::Post {
        let _ = req.as_reader().take(MAX_BODY).read_to_string(&mut body);
    }
    let (status, ctype, mut out) = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        route(&method, &url, &body, chain_id, rest)
    }))
    .unwrap_or((500, "application/json", "{\"error\":\"wrong password or internal error\"}".to_string()));

    if url == "/" && ctype == "text/html" {
        out = out.replace("__CSRF_TOKEN__", token);
    }

    let mut resp = tiny_http::Response::from_string(out).with_status_code(status);
    resp.add_header(tiny_http::Header::from_bytes(&b"Content-Type"[..], ctype.as_bytes()).unwrap());
    resp.add_header(tiny_http::Header::from_bytes(&b"Cache-Control"[..], &b"no-store, must-revalidate"[..]).unwrap());
    resp.add_header(
        tiny_http::Header::from_bytes(
            &b"Content-Security-Policy"[..],
            &b"default-src 'self'; script-src 'self' 'unsafe-inline'; style-src 'self' 'unsafe-inline'; connect-src 'self'; img-src 'self' data:"[..],
        )
        .unwrap(),
    );
    let _ = req.respond(resp);
}

const DASHBOARD_HTML: &str = r##"<!doctype html><html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1"><title>Sequora Wallet</title>
<style>
*{box-sizing:border-box;margin:0;padding:0;border-radius:0}
:root{--ac:#6c5cff;--bg:#0a0a0e;--ink:#f2f2f6;--mut:#9696a6;--faint:#5e5e72;--card:#0f0f15;--line:rgba(255,255,255,.12);--line2:rgba(255,255,255,.22);--mono:ui-monospace,SFMono-Regular,Menlo,Consolas,monospace}
body{font-family:system-ui,-apple-system,'Segoe UI',Roboto,sans-serif;min-height:100vh;color:var(--ink);display:flex;justify-content:center;padding:28px 14px;background:var(--bg)}
body::before{content:"";position:fixed;inset:0;z-index:-2;background:radial-gradient(800px 420px at 50% -60px,rgba(108,92,255,.13),transparent 70%),var(--bg)}
body::after{content:"";position:fixed;inset:0;z-index:-1;pointer-events:none;opacity:.5;background-image:linear-gradient(rgba(255,255,255,.028) 1px,transparent 1px),linear-gradient(90deg,rgba(255,255,255,.028) 1px,transparent 1px);background-size:44px 44px}
.app{width:100%;max-width:440px}
.top{display:flex;align-items:center;justify-content:space-between;margin-bottom:18px}
.brand{display:flex;align-items:center;gap:10px;font-weight:800;font-size:16px;letter-spacing:1px;text-transform:uppercase}
.logo{width:28px;height:28px;background-image:url('data:image/png;base64,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');background-size:contain;background-repeat:no-repeat;background-position:center}
.net{font-family:var(--mono);font-size:11px;letter-spacing:.5px;color:var(--mut);background:transparent;border:1px solid var(--line);padding:5px 10px;text-transform:uppercase}
.hero{background:var(--card);border:1px solid var(--line2);padding:22px;position:relative;overflow:hidden}
.hero:after{content:"";position:absolute;right:0;top:0;width:3px;height:100%;background:var(--ac)}
.hero .lbl{font-family:var(--mono);font-size:11px;letter-spacing:.5px;text-transform:uppercase;color:var(--mut)}
.hero .amt{font-size:38px;font-weight:800;letter-spacing:-1px;margin:6px 0 2px}
.hero .amt small{font-size:18px;font-weight:600;color:var(--mut)}
.hero .addr{font-size:11px;font-family:var(--mono);color:var(--ink);background:#0c0c12;border:1px solid var(--line);padding:7px 10px;margin-top:12px;display:inline-flex;gap:8px;align-items:center;cursor:pointer}
.tabs{display:flex;gap:0;border:1px solid var(--line);margin:18px 0}
.tab{flex:1;text-align:center;padding:11px;font-weight:700;font-size:13px;letter-spacing:.5px;text-transform:uppercase;color:var(--mut);cursor:pointer;border-right:1px solid var(--line)}
.tab:last-child{border-right:0}
.tab.on{background:var(--ac);color:#fff}
.card{background:var(--card);border:1px solid var(--line);padding:16px;margin-bottom:12px}
.card h3{font-family:var(--mono);font-size:11px;color:var(--mut);font-weight:700;margin-bottom:10px;text-transform:uppercase;letter-spacing:.6px}
.asset{display:flex;align-items:center;gap:12px}
.coin{width:40px;height:40px;background:var(--ac);display:flex;align-items:center;justify-content:center;font-weight:800;font-size:12px;color:#fff}
.asset .nm{font-weight:700}.asset .sub{font-size:12px;color:var(--mut)}.asset .val{margin-left:auto;text-align:right;font-weight:800}
label{font-family:var(--mono);font-size:11px;letter-spacing:.4px;text-transform:uppercase;color:var(--mut);display:block;margin:12px 0 5px}
input{width:100%;background:#0c0c12;color:var(--ink);border:1px solid var(--line);padding:11px 12px;font-size:14px;font-family:inherit;outline:none}
input:focus{border-color:var(--ac)}
.btn{width:100%;background:var(--ac);color:#fff;border:1px solid var(--ac);padding:13px;font-size:13px;font-weight:700;letter-spacing:.5px;text-transform:uppercase;cursor:pointer;margin-top:14px;transition:background .15s}
.btn:hover{background:#5a48f0}
.btn.sm{width:auto;padding:9px 16px;margin:0}.btn.alt{background:transparent;color:var(--ink);border-color:var(--line2)}
.btn.alt:hover{border-color:var(--ac)}
.vrow{display:flex;align-items:center;gap:10px;padding:11px 0;border-bottom:1px solid var(--line)}.vrow:last-child{border:0}
.vrow .vn{font-weight:700;font-size:14px}.vrow .vs{font-size:11px;color:var(--mut);font-family:var(--mono)}
.unlock{display:flex;gap:8px;align-items:center;background:var(--card);border:1px solid var(--line);padding:6px 12px;margin-bottom:12px}
.unlock input{border:0;background:transparent;padding:7px}
.foot{text-align:center;font-family:var(--mono);font-size:10px;letter-spacing:.4px;text-transform:uppercase;color:var(--faint);margin-top:18px}.hide{display:none!important}
#toast{position:fixed;left:50%;bottom:24px;transform:translateX(-50%) translateY(90px);background:#14141c;border:1px solid var(--line2);padding:13px 18px;max-width:400px;transition:transform .35s;z-index:9}
#toast.show{transform:translateX(-50%) translateY(0)}
#toast.ok{border-color:var(--ac)}#toast.err{border-color:#ff5a5a}
#toast .h{font-weight:700;margin-bottom:3px;font-size:13px}#toast .m{color:var(--mut);font-family:var(--mono);font-size:11px;word-break:break-all}
#lock{position:fixed;inset:0;display:flex;align-items:center;justify-content:center;padding:24px;z-index:20;background:var(--bg)}
#lock .box{width:100%;max-width:360px;background:var(--card);border:1px solid var(--line2);padding:34px 26px;text-align:center}
#lock .logo{width:52px;height:52px;margin:0 auto 16px;font-size:26px}
#lock h1{font-size:20px;font-weight:800;letter-spacing:1px;text-transform:uppercase}
#lock .tag{font-family:var(--mono);font-size:11px;color:var(--mut);margin:6px 0 22px;letter-spacing:.3px}
#lock input{text-align:center;font-size:15px;padding:13px}
#lock .err{color:#ff7a7a;font-size:12px;min-height:16px;margin-top:12px}
.lockbtn{cursor:pointer;user-select:none}
#confirm{position:fixed;inset:0;display:flex;align-items:center;justify-content:center;padding:24px;z-index:25;background:rgba(8,6,16,.82)}
#confirm .box{width:100%;max-width:360px;background:var(--card);border:1px solid var(--line2);padding:24px}
#confirm h3{font-size:16px;font-weight:800;margin-bottom:6px;letter-spacing:.3px}
#confirm .cfsub{font-size:12px;color:var(--mut);margin-bottom:12px}
.cfrow{display:flex;justify-content:space-between;gap:12px;padding:10px 0;border-bottom:1px solid var(--line);font-size:13px}
.cfrow:last-child{border:0}.cfrow span{color:var(--mut);white-space:nowrap;font-family:var(--mono);font-size:11px;text-transform:uppercase}.cfrow b{text-align:right;word-break:break-all;font-family:var(--mono)}
#confirm .acts{display:flex;gap:10px;margin-top:16px}#confirm .acts .btn{flex:1;margin-top:0}
</style></head><body>
<div id="lock"><div class="box">
  <div class="logo"></div>
  <h1>Sequora</h1>
  <div style="position:relative">
    <input id="lpw" type="password" placeholder="password" autocomplete="off" autocapitalize="off" autocorrect="off" spellcheck="false" onkeydown="if(event.key==='Enter')unlock()">
    <span id="eye" onclick="toggleEye()" style="position:absolute;right:12px;top:50%;transform:translateY(-50%);cursor:pointer;user-select:none;font-size:15px;opacity:.65" title="show / hide">show</span>
  </div>
  <div id="lcount" style="font-size:11px;color:#6f6b8c;margin-top:6px;min-height:14px"></div>
  <button class="btn" onclick="unlock()">Unlock</button>
  <div class="err" id="lerr"></div>
  <div id="reclink" onclick="showRec()" style="font-size:12px;color:#8a8fb8;margin-top:16px;cursor:pointer">↩ Recover a wallet from your 24-word phrase</div>
  <div id="rec" class="hide" style="margin-top:14px;text-align:left">
    <label style="font-size:12px;color:#9a96b8;display:block;margin-bottom:4px">24-word recovery phrase</label>
    <textarea id="rphrase" rows="3" placeholder="word1 word2 word3 …" style="width:100%;background:rgba(0,0,0,.25);color:#eceaf5;border:1px solid rgba(255,255,255,.1);border-radius:11px;padding:11px 12px;font-size:13px;font-family:ui-monospace,monospace;resize:vertical;outline:none"></textarea>
    <label style="font-size:12px;color:#9a96b8;display:block;margin:10px 0 4px">New password for this device</label>
    <input id="rpw" type="password" placeholder="set a password" autocomplete="off">
    <label style="font-size:11px;color:#9a96b8;display:flex;gap:7px;margin-top:10px;align-items:flex-start"><input type="checkbox" id="rack" style="width:auto;margin-top:2px"><span>I understand this replaces any wallet currently stored on this device.</span></label>
    <button class="btn" onclick="restore()">Restore wallet</button>
  </div>
  <div id="newlink" onclick="showNew()" style="font-size:12px;color:#8a8fb8;margin-top:10px;cursor:pointer">+ Create a new wallet</div>
  <div id="newbox" class="hide" style="margin-top:14px;text-align:left">
    <label style="font-size:12px;color:#9a96b8;display:block;margin-bottom:4px">New password for this device</label>
    <input id="npw" type="password" placeholder="set a password" autocomplete="off">
    <label style="font-size:12px;color:#9a96b8;display:block;margin:10px 0 4px">Confirm password</label>
    <input id="npw2" type="password" placeholder="repeat password" autocomplete="off">
    <label style="font-size:11px;color:#9a96b8;display:flex;gap:7px;margin-top:10px;align-items:flex-start"><input type="checkbox" id="nack" style="width:auto;margin-top:2px"><span>I understand this replaces any wallet on this device, and I will write down the recovery phrase.</span></label>
    <button class="btn" id="newbtn" onclick="createWallet()">Create wallet</button>
    <div class="err" id="newerr" style="min-height:16px;margin-top:8px"></div>
    <div id="newresult" class="hide" style="margin-top:14px">
      <div style="font-size:11px;color:#ffb070;line-height:1.5">&#9888; WRITE THESE 24 WORDS DOWN — on paper, offline. They are the ONLY way to recover this wallet. Never share them; never store them online.</div>
      <div id="newphrase" style="margin-top:8px;background:#0c0c12;border:1px solid var(--line2);padding:11px;font-family:var(--mono);font-size:13px;line-height:1.7;word-spacing:3px"></div>
      <div id="newaddr" style="margin-top:8px;font-family:var(--mono);font-size:11px;color:var(--mut);word-break:break-all"></div>
      <label style="font-size:11px;color:#9a96b8;display:flex;gap:7px;margin-top:10px;align-items:flex-start"><input type="checkbox" id="savedack" style="width:auto;margin-top:2px"><span>I have written down my 24 words and stored them safely.</span></label>
      <button class="btn" onclick="newContinue()">Continue to wallet</button>
    </div>
  </div>
</div></div>
<div class="app hide" id="app">
 <div class="top"><div class="brand"><div class="logo"></div>Sequora</div><div style="display:flex;gap:8px;align-items:center"><div class="net">● sequora-wasm</div><div class="net lockbtn" onclick="lock()">LOCK</div></div></div>
 <div class="hero">
   <div class="lbl">Total balance · post-quantum secured</div>
   <div class="amt"><span id="bal">0</span> <small>SQR</small></div>
   <div class="addr" id="addr" onclick="copyAddr()" title="click to copy">…</div>
 </div>
 <div class="tabs"><div class="tab on" id="tw" onclick="tab('w')">Wallet</div><div class="tab" id="ts" onclick="tab('s')">Stake</div><div class="tab" id="tv" onclick="tab('v')">Validator</div></div>
 <div id="vw">
   <div class="card"><div class="asset"><div class="coin">SQR</div><div><div class="nm">Sequora</div><div class="sub">ML-DSA-65 · quantum-safe</div></div><div class="val"><span id="bal2">0</span><div class="sub">SQR</div></div></div></div>
   <div class="card"><h3>Send</h3>
     <label>Recipient address</label><input id="sendTo" placeholder="sqr1…">
     <label>Amount (SQR)</label><input id="sendAmt" placeholder="0.00" inputmode="decimal">
     <button class="btn" onclick="send()">Send SQR</button></div>
 </div>
 <div id="vs2" class="hide">
   <div class="card"><h3>Staking rewards</h3><div class="asset"><div class="coin">+</div><div><div class="nm"><span id="rew">0</span> SQR</div><div class="sub">pending across delegations</div></div></div></div>
   <div class="card"><h3>Your delegations</h3><div id="dels"></div></div>
   <div class="card"><h3>Validators</h3><div id="vals"></div></div>
 </div>
 <div id="vval" class="hide">
   <div class="card"><h3>My validator</h3><div id="myval"><div class="vs">loading…</div></div></div>
   <div class="card"><h3>Network validators</h3><div id="netvals"></div></div>
 </div>
 <div class="foot">non-custodial · keys encrypted (Argon2id) · no backdoors</div>
</div>
<div id="confirm" class="hide"><div class="box">
  <h3 id="cfTitle">Confirm transaction</h3>
  <div class="cfsub">Review the details — this will be signed with your post-quantum key.</div>
  <div id="cfRows"></div>
  <div class="acts"><button class="btn alt" onclick="cancelConfirm()">Cancel</button><button class="btn" onclick="doConfirm()">Confirm &amp; sign</button></div>
</div></div>
<div id="toast"><div class="h" id="th"></div><div class="m" id="tm"></div></div>
<script>
const TOKEN='__CSRF_TOKEN__';
const $=id=>document.getElementById(id);
const sqr=u=>(parseInt(u||0)/1e6).toLocaleString(undefined,{maximumFractionDigits:6});
const usqr=s=>Math.round(parseFloat(s||'0')*1e6).toString();
// HTML-escape on-chain data (e.g. validator monikers) before it touches innerHTML.
// This is the real XSS defense — without it a validator could set a moniker like
// "<img onerror=...>" and run script that reads your in-memory password.
const esc=s=>String(s==null?'':s).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
// SECURITY: the password lives ONLY in this in-memory variable for the unlocked
// session — never localStorage/cookie/sessionStorage. It is wiped on lock, on
// idle timeout, and never survives a refresh. The server still decrypts the key
// per-action and zeroizes it; nothing keeps the key unlocked between requests.
let PW='';let ADDR='';let idleTimer=null;let started=false;let intv=null;
const IDLE_MS=5*60*1000; // auto-lock after 5 min of inactivity
function resetIdle(){clearTimeout(idleTimer);if(PW)idleTimer=setTimeout(lock,IDLE_MS)}
async function unlock(){
  // Trim surrounding whitespace — pasting a password often drags along a trailing
  // space or newline, which would otherwise be a "wrong password" with no clue why.
  const p=$('lpw').value.trim();
  if(!p){$('lerr').textContent='enter your password';return}
  $('lerr').textContent='unlocking…';
  try{
    const resp=await fetch('/api/unlock',{method:'POST',headers:{'X-Sequora-Token':TOKEN,'Content-Type':'application/json'},body:JSON.stringify({password:p})});
    const r=await resp.json();
    if(r.ok){PW=p;$('lpw').value='';$('lerr').textContent='';
      $('lock').classList.add('hide');$('app').classList.remove('hide');
      if(!started){started=true;refresh();intv=setInterval(refresh,15000)}else{refresh()}
      resetIdle();
    }else{$('lerr').textContent=r.error||'wrong password';$('lpw').select()}
  }catch(e){$('lerr').textContent='could not reach wallet'}
}
function lock(){PW='';clearTimeout(idleTimer);clearInterval(intv);intv=null;started=false;$('app').classList.add('hide');$('lock').classList.remove('hide');$('lpw').value='';$('lcount').textContent='';$('lpw').focus()}
function toggleEye(){const i=$('lpw');i.type=i.type==='password'?'text':'password'}
function showRec(){$('rec').classList.toggle('hide')}
async function restore(){
  const ph=$('rphrase').value.trim().replace(/\s+/g,' '), rp=$('rpw').value;
  if(!ph){$('lerr').textContent='enter your 24-word recovery phrase';return}
  if(!rp){$('lerr').textContent='set a password for this device';return}
  if(!$('rack').checked){$('lerr').textContent='please tick the confirmation box';return}
  $('lerr').textContent='restoring…';
  try{
    const r=await (await fetch('/api/restore',{method:'POST',headers:{'X-Sequora-Token':TOKEN,'Content-Type':'application/json'},body:JSON.stringify({mnemonic:ph,password:rp})})).json();
    if(r.ok){PW=rp;$('rphrase').value='';$('rpw').value='';$('rack').checked=false;$('lerr').textContent='';
      $('lock').classList.add('hide');$('app').classList.remove('hide');
      if(!started){started=true;refresh();intv=setInterval(refresh,15000)}else{refresh()}
      resetIdle();toast('ok','Wallet restored ✓',r.address||'');
    }else{$('lerr').textContent=r.error||'restore failed'}
  }catch(e){$('lerr').textContent='could not reach wallet'}
}
function showNew(){$('newbox').classList.toggle('hide');$('rec').classList.add('hide')}
async function createWallet(){
  const p=$('npw').value, p2=$('npw2').value;
  if(!p){$('newerr').textContent='set a password';return}
  if(p!==p2){$('newerr').textContent='passwords do not match';return}
  if(!$('nack').checked){$('newerr').textContent='please tick the confirmation box';return}
  $('newerr').textContent='creating…';
  try{
    const r=await (await fetch('/api/new',{method:'POST',headers:{'X-Sequora-Token':TOKEN,'Content-Type':'application/json'},body:JSON.stringify({password:p})})).json();
    if(r.ok){PW=p;$('npw').value='';$('npw2').value='';$('newerr').textContent='';
      $('newphrase').textContent=r.mnemonic||'';      // textContent (not innerHTML) — no injection
      $('newaddr').textContent=r.address||'';
      $('newbtn').classList.add('hide');$('newresult').classList.remove('hide');
    }else{$('newerr').textContent=r.error||'could not create wallet'}
  }catch(e){$('newerr').textContent='could not reach wallet'}
}
function newContinue(){
  if(!$('savedack').checked){$('newerr').textContent='please tick "I have written down my 24 words" first';return}
  $('newphrase').textContent='';$('savedack').checked=false;$('nack').checked=false;$('newerr').textContent='';   // wipe phrase from the DOM
  $('newbox').classList.add('hide');$('newresult').classList.add('hide');$('newbtn').classList.remove('hide');
  $('lock').classList.add('hide');$('app').classList.remove('hide');
  if(!started){started=true;refresh();intv=setInterval(refresh,15000)}else{refresh()}
  resetIdle();toast('ok','Wallet created',ADDR||'');
}
['click','keydown','touchstart'].forEach(e=>document.addEventListener(e,resetIdle));
document.addEventListener('DOMContentLoaded',()=>{const i=$('lpw');if(i)i.addEventListener('input',()=>{const n=i.value.length;$('lcount').textContent=n?(n+' character'+(n==1?'':'s')):''})});
function tab(t){$('vw').classList.toggle('hide',t!='w');$('vs2').classList.toggle('hide',t!='s');$('vval').classList.toggle('hide',t!='v');$('tw').classList.toggle('on',t=='w');$('ts').classList.toggle('on',t=='s');$('tv').classList.toggle('on',t=='v')}
function copyAddr(){navigator.clipboard.writeText(ADDR);toast('ok','Address copied',ADDR)}
function toast(k,h,m){let t=$('toast');t.className='show '+k;$('th').textContent=h;$('tm').textContent=m||'';setTimeout(()=>t.className=t.className.replace('show',''),4500)}
async function refresh(){
  let resp=await fetch('/api/info',{headers:{'X-Sequora-Token':TOKEN}});
  if(!resp.ok){ // stale token / forbidden — stop hammering and reload a fresh page
    if(intv){clearInterval(intv);intv=null}
    toast('err','Session expired','reloading…');setTimeout(()=>location.reload(),900);return;
  }
  let d=await resp.json();
  if(!d||!d.address){return}
  ADDR=d.address;
  $('addr').innerHTML=d.address.slice(0,14)+'…'+d.address.slice(-6)+' ⧉';
  $('bal').textContent=sqr(d.balance);$('bal2').textContent=sqr(d.balance);$('rew').textContent=sqr(d.rewards);
  $('vals').innerHTML=d.validators.map(v=>`<div class="vrow"><div class="coin" style="width:34px;height:34px;font-size:11px">V</div><div><div class="vn">${esc(v.moniker)}</div><div class="vs">${sqr(v.tokens)} SQR staked</div></div><div style="margin-left:auto;display:flex;gap:6px"><input id="amt_${esc(v.valoper)}" placeholder="SQR" style="width:78px;padding:8px"><button class="btn sm" onclick="stake('${esc(v.valoper)}')">Stake</button></div></div>`).join('')||'<div class="vs">none</div>';
  $('dels').innerHTML=d.delegations.map(x=>`<div class="vrow"><div><div class="vn">${sqr(x.amount)} SQR</div><div class="vs">${esc(x.valoper).slice(0,20)}…</div></div><button class="btn sm alt" style="margin-left:auto" onclick="claim('${esc(x.valoper)}')">Claim</button></div>`).join('')||'<div class="vs">no delegations yet</div>';
  // ---- Validator tab ----
  const badge=s=>{const a=String(s||'');const on=a.includes('BONDED');return '<span style="font-size:10px;padding:3px 8px;border-radius:20px;background:'+(on?'rgba(80,220,140,.18)':'rgba(255,150,80,.18)')+';color:'+(on?'#5fe0a0':'#ffb070')+'">'+(on?'ACTIVE':(esc(a.replace('BOND_STATUS_',''))||'INACTIVE'))+'</span>'};
  const mv=d.myvalidator||{exists:false};
  if(mv.exists){
    const jailed=mv.jailed===true;
    const st=jailed?'<span style="color:#ff7a7a;font-size:11px">⚠ JAILED</span>':badge(mv.status);
    $('myval').innerHTML='<div class="vrow"><div><div class="vn">'+esc(mv.moniker)+' '+st+'</div><div class="vs">'+sqr(mv.tokens)+' SQR bonded · commission '+(parseFloat(mv.commission||0)*100).toFixed(1)+'%</div></div></div>'
      +'<div style="display:flex;gap:8px;margin-top:10px"><button class="btn sm" onclick="withdrawCommission()">Withdraw commission</button>'+(jailed?'<button class="btn sm alt" onclick="unjail()">Unjail</button>':'')+'</div>';
  }else{
    $('myval').innerHTML='<div class="vs">This wallet is not operating a validator.<br>To run one, use the setup wizard (<code>scripts/validator-wizard.sh</code>) — this wallet would be the operator key. Your valoper address:<br><span style="font-family:ui-monospace,monospace;font-size:10px">'+esc(d.myvaloper||'')+'</span></div>';
  }
  $('netvals').innerHTML=(d.validators||[]).map(function(v){var bs=v.jailed===true?'<span style="color:#ff7a7a;font-size:10px">JAILED</span>':badge(v.status);return '<div class="vrow"><div class="coin" style="width:30px;height:30px;font-size:10px">V</div><div><div class="vn">'+esc(v.moniker)+' '+bs+'</div><div class="vs">'+sqr(v.tokens)+' SQR · '+(parseFloat(v.commission||0)*100).toFixed(1)+'% commission</div></div></div>'}).join('')||'<div class="vs">none</div>';
}
async function post(path,obj,label){
  if(!PW){lock();return}
  obj.password=PW;
  let d=await (await fetch(path,{method:'POST',headers:{'X-Sequora-Token':TOKEN,'Content-Type':'application/json'},body:JSON.stringify(obj)})).json();
  if(d.error||(d.code&&d.code!=0))toast('err',label+' failed',d.error||d.log||('code '+d.code));
  else toast('ok',label+' sent ✓','tx '+(d.txhash||'').slice(0,28)+'…');
  setTimeout(refresh,3500);
}
// WYSIWYS: nothing is signed until the user sees the exact details and confirms.
let pendingTx=null;
function confirmTx(title,rows,path,obj){
  if(!PW){lock();return}
  $('cfTitle').textContent=title;
  $('cfRows').innerHTML=rows.map(r=>'<div class="cfrow"><span>'+esc(r[0])+'</span><b>'+esc(r[1])+'</b></div>').join('');
  pendingTx={path:path,obj:obj,label:title};
  $('confirm').classList.remove('hide');
}
function cancelConfirm(){$('confirm').classList.add('hide');pendingTx=null}
function doConfirm(){const t=pendingTx;pendingTx=null;$('confirm').classList.add('hide');if(t)post(t.path,t.obj,t.label)}
function send(){
  const to=$('sendTo').value.trim(),a=$('sendAmt').value.trim();
  if(!to||!a){toast('err','Send','enter a recipient and amount');return}
  confirmTx('Send SQR',[['To',to],['Amount',a+' SQR'],['Network fee','~0.012 SQR']],'/api/send',{to:to,amount:usqr(a)});
}
function stake(v){
  const a=($('amt_'+v).value||'').trim();
  if(!a){toast('err','Stake','enter an amount');return}
  confirmTx('Stake (delegate)',[['Validator',v.slice(0,16)+'…'+v.slice(-6)],['Amount',a+' SQR'],['Network fee','~0.015 SQR']],'/api/stake',{valoper:v,amount:usqr(a)});
}
function claim(v){confirmTx('Claim staking rewards',[['From validator',v.slice(0,16)+'…'+v.slice(-6)],['Network fee','~0.009 SQR']],'/api/claim',{valoper:v})}
function unjail(){confirmTx('Unjail your validator',[['Action','remove downtime jail'],['Network fee','~0.006 SQR']],'/api/unjail',{})}
function withdrawCommission(){confirmTx('Withdraw validator commission',[['Action','withdraw earned commission'],['Network fee','~0.009 SQR']],'/api/withdraw-commission',{})}
$('lpw').focus(); // refresh starts only after unlock (see unlock())
</script></body></html>"##;

fn main() {
    let args: Vec<String> = env::args().collect();
    match args.get(1).map(String::as_str).unwrap_or("help") {
        "new" => cmd_new(),
        "restore" => cmd_restore(),
        "address" => cmd_address(),
        "balance" => cmd_balance(args.get(2).map(String::as_str).unwrap_or("http://localhost:1317")),
        "sign" => cmd_sign(args.get(2).map(String::as_str).unwrap_or("hello-sequora")),
        "serve" => {
            let port: u16 = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(8088);
            let chain_id = args.get(3).map(String::as_str).unwrap_or("sequora-wasm");
            let rest = args.get(4).map(String::as_str).unwrap_or("http://localhost:1317");
            cmd_serve(port, chain_id, rest);
        }
        "stake" => {
            let valoper = args.get(2).map(String::as_str).expect("usage: sqrwallet stake <valoper> <amount> [chain_id] [rest_url]");
            let amount = args.get(3).map(String::as_str).expect("usage: sqrwallet stake <valoper> <amount> [chain_id] [rest_url]");
            let chain_id = args.get(4).map(String::as_str).unwrap_or("sequora-wasm");
            let rest = args.get(5).map(String::as_str).unwrap_or("http://localhost:1317");
            cmd_stake(rest, chain_id, valoper, amount);
        }
        "send" => {
            let to = args.get(2).map(String::as_str).expect("usage: sqrwallet send <to_addr> <amount> [chain_id] [rest_url]");
            let amount = args.get(3).map(String::as_str).expect("usage: sqrwallet send <to_addr> <amount> [chain_id] [rest_url]");
            let chain_id = args.get(4).map(String::as_str).unwrap_or("sequora-wasm");
            let rest = args.get(5).map(String::as_str).unwrap_or("http://localhost:1317");
            cmd_send(rest, chain_id, to, amount);
        }
        "claim" => {
            let valoper = args.get(2).map(String::as_str).expect("usage: sqrwallet claim <valoper> [chain_id] [rest_url]");
            let chain_id = args.get(3).map(String::as_str).unwrap_or("sequora-wasm");
            let rest = args.get(4).map(String::as_str).unwrap_or("http://localhost:1317");
            cmd_claim(rest, chain_id, valoper);
        }
        "unstake" => {
            let valoper = args.get(2).map(String::as_str).expect("usage: sqrwallet unstake <valoper> <amount> [chain_id] [rest_url]");
            let amount = args.get(3).map(String::as_str).expect("usage: sqrwallet unstake <valoper> <amount> [chain_id] [rest_url]");
            let chain_id = args.get(4).map(String::as_str).unwrap_or("sequora-wasm");
            let rest = args.get(5).map(String::as_str).unwrap_or("http://localhost:1317");
            cmd_unstake(rest, chain_id, valoper, amount);
        }
        _ => {
            println!("Sequora wallet (Rust shared-core prototype)");
            println!("  sqrwallet new                 generate a wallet + 24-word recovery phrase");
            println!("  sqrwallet restore             recover a wallet (SQRWALLET_MNEMONIC + SQRWALLET_PASSWORD)");
            println!("  sqrwallet address             print this wallet's address");
            println!("  sqrwallet balance [rest_url]  query balance (default http://localhost:1317)");
        }
    }
}
