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
fn save_wallet_from_seed(seed: &[u8; 32], password: &str) -> String {
    let (pk, _sk) = ml_dsa_65::KG::keygen_from_seed(seed);
    let pk_bytes = pk.into_bytes();
    let addr = derive_address(&pk_bytes);

    // Never silently destroy an existing wallet: if key.json is present, back it
    // up (0600 perms are preserved by the copy) before overwriting. A mistaken
    // `new`/restore is then recoverable. (audit: destructive /api/restore)
    if key_path().exists() {
        let _ = fs::copy(key_path(), key_path().with_extension("json.bak"));
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
    addr
}

fn cmd_new() {
    let password = get_password();
    // 32 bytes of entropy = the FIPS-204 seed AND the 24-word recovery phrase.
    let mut entropy = rand_bytes(32);
    let mnemonic = bip39::Mnemonic::from_entropy(&entropy).expect("mnemonic");
    let mut seed = [0u8; 32];
    seed.copy_from_slice(&entropy);
    let addr = save_wallet_from_seed(&seed, &password);
    seed.zeroize();
    entropy.zeroize();

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
    let phrase = env::var("SQRWALLET_MNEMONIC")
        .expect("set SQRWALLET_MNEMONIC to your 24-word recovery phrase (and SQRWALLET_PASSWORD to a new password)");
    let mnemonic = bip39::Mnemonic::parse(phrase.trim())
        .expect("invalid recovery phrase — check the words and their order");
    let entropy = mnemonic.to_entropy();
    if entropy.len() != 32 {
        panic!("expected a 24-word recovery phrase");
    }
    let mut seed = [0u8; 32];
    seed.copy_from_slice(&entropy);
    let addr = save_wallet_from_seed(&seed, &password);
    seed.zeroize();

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
        let (_pk, sk) = ml_dsa_65::KG::keygen_from_seed(&seed);
        seed.zeroize();
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
    let phrase = v["mnemonic"].as_str().unwrap_or("").trim().to_string();
    let pw = v["password"].as_str().unwrap_or("");
    if phrase.is_empty() || pw.is_empty() {
        return (200, "application/json", "{\"ok\":false,\"error\":\"recovery phrase and a new password are both required\"}".into());
    }
    let mnemonic = match bip39::Mnemonic::parse(phrase) {
        Ok(m) => m,
        Err(_) => return (200, "application/json", "{\"ok\":false,\"error\":\"invalid recovery phrase — check the words and order\"}".into()),
    };
    let entropy = mnemonic.to_entropy();
    if entropy.len() != 32 {
        return (200, "application/json", "{\"ok\":false,\"error\":\"expected a 24-word recovery phrase\"}".into());
    }
    let mut seed = [0u8; 32];
    seed.copy_from_slice(&entropy);
    let addr = save_wallet_from_seed(&seed, pw);
    seed.zeroize();
    (200, "application/json", serde_json::json!({"ok": true, "address": addr}).to_string())
}

fn route(method: &tiny_http::Method, url: &str, body: &str, chain_id: &str, rest: &str) -> (u16, &'static str, String) {
    match (method, url) {
        (tiny_http::Method::Get, "/") => (200, "text/html", DASHBOARD_HTML.to_string()),
        (tiny_http::Method::Get, "/api/info") => (200, "application/json", info_json(rest)),
        (tiny_http::Method::Post, "/api/unlock") => api_unlock(body),
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
*{box-sizing:border-box;margin:0;padding:0}
body{font-family:'Inter',system-ui,sans-serif;min-height:100vh;color:#eceaf5;display:flex;justify-content:center;padding:28px 14px;
 background:radial-gradient(1200px 600px at 50% -10%,#2a1f4d 0%,#14111f 55%,#0b0a12 100%)}
.app{width:100%;max-width:440px}
.top{display:flex;align-items:center;justify-content:space-between;margin-bottom:18px}
.brand{display:flex;align-items:center;gap:10px;font-weight:700;font-size:17px}
.logo{width:30px;height:30px;border-radius:9px;background:linear-gradient(135deg,#8a5cff,#5b8dff);display:flex;align-items:center;justify-content:center;font-size:16px;box-shadow:0 4px 14px rgba(138,92,255,.45)}
.net{font-size:11px;color:#a8a4c4;background:rgba(255,255,255,.06);border:1px solid rgba(255,255,255,.08);padding:4px 10px;border-radius:20px}
.hero{background:linear-gradient(135deg,#7b5cff 0%,#5b8dff 100%);border-radius:22px;padding:22px;box-shadow:0 16px 40px rgba(91,141,255,.30);position:relative;overflow:hidden}
.hero:after{content:"";position:absolute;right:-40px;top:-40px;width:160px;height:160px;border-radius:50%;background:rgba(255,255,255,.12)}
.hero .lbl{font-size:12px;color:rgba(255,255,255,.85);font-weight:500}
.hero .amt{font-size:38px;font-weight:800;letter-spacing:-1px;margin:4px 0 2px}
.hero .amt small{font-size:18px;font-weight:600;opacity:.85}
.hero .addr{font-size:11px;font-family:ui-monospace,monospace;color:rgba(255,255,255,.9);background:rgba(0,0,0,.18);padding:6px 10px;border-radius:10px;margin-top:12px;display:inline-flex;gap:8px;align-items:center;cursor:pointer}
.tabs{display:flex;gap:6px;background:rgba(255,255,255,.05);border-radius:14px;padding:5px;margin:18px 0}
.tab{flex:1;text-align:center;padding:9px;border-radius:10px;font-weight:600;font-size:14px;color:#a8a4c4;cursor:pointer}
.tab.on{background:linear-gradient(135deg,#8a5cff,#5b8dff);color:#fff;box-shadow:0 4px 12px rgba(138,92,255,.4)}
.card{background:rgba(255,255,255,.04);border:1px solid rgba(255,255,255,.08);border-radius:16px;padding:16px;margin-bottom:12px}
.card h3{font-size:12px;color:#bdb8da;font-weight:600;margin-bottom:10px;text-transform:uppercase;letter-spacing:.6px}
.asset{display:flex;align-items:center;gap:12px}
.coin{width:40px;height:40px;border-radius:50%;background:linear-gradient(135deg,#8a5cff,#5b8dff);display:flex;align-items:center;justify-content:center;font-weight:800;font-size:12px;color:#fff}
.asset .nm{font-weight:600}.asset .sub{font-size:12px;color:#9a96b8}.asset .val{margin-left:auto;text-align:right;font-weight:700}
label{font-size:12px;color:#9a96b8;display:block;margin:10px 0 4px}
input{width:100%;background:rgba(0,0,0,.25);color:#eceaf5;border:1px solid rgba(255,255,255,.1);border-radius:11px;padding:11px 12px;font-size:14px;font-family:inherit;outline:none}
input:focus{border-color:#7b5cff;box-shadow:0 0 0 3px rgba(123,92,255,.2)}
.btn{width:100%;background:linear-gradient(135deg,#8a5cff,#5b8dff);color:#fff;border:0;border-radius:12px;padding:12px;font-size:14px;font-weight:700;cursor:pointer;margin-top:12px;transition:transform .08s,box-shadow .2s;box-shadow:0 6px 18px rgba(123,92,255,.35)}
.btn:hover{transform:translateY(-1px);box-shadow:0 10px 24px rgba(123,92,255,.5)}
.btn.sm{width:auto;padding:8px 14px;margin:0;font-size:13px}.btn.alt{background:rgba(255,255,255,.09);box-shadow:none}
.vrow{display:flex;align-items:center;gap:10px;padding:10px 0;border-bottom:1px solid rgba(255,255,255,.06)}.vrow:last-child{border:0}
.vrow .vn{font-weight:600;font-size:14px}.vrow .vs{font-size:11px;color:#9a96b8}
.unlock{display:flex;gap:8px;align-items:center;background:rgba(255,255,255,.04);border:1px solid rgba(255,255,255,.08);border-radius:12px;padding:6px 12px;margin-bottom:12px}
.unlock input{border:0;background:transparent;padding:7px;box-shadow:none}
.foot{text-align:center;font-size:11px;color:#6f6b8c;margin-top:18px}.hide{display:none!important}
#toast{position:fixed;left:50%;bottom:24px;transform:translateX(-50%) translateY(90px);background:#1c1830;border:1px solid rgba(255,255,255,.12);border-radius:14px;padding:13px 18px;max-width:400px;box-shadow:0 12px 40px rgba(0,0,0,.5);transition:transform .35s;z-index:9}
#toast.show{transform:translateX(-50%) translateY(0)}
#toast.ok{border-color:rgba(80,220,140,.55)}#toast.err{border-color:rgba(255,90,90,.55)}
#toast .h{font-weight:700;margin-bottom:3px;font-size:13px}#toast .m{color:#a8a4c4;font-family:ui-monospace,monospace;font-size:11px;word-break:break-all}
#lock{position:fixed;inset:0;display:flex;align-items:center;justify-content:center;padding:24px;z-index:20;
 background:radial-gradient(1200px 600px at 50% -10%,#2a1f4d 0%,#14111f 55%,#0b0a12 100%)}
#lock .box{width:100%;max-width:360px;background:rgba(255,255,255,.04);border:1px solid rgba(255,255,255,.08);border-radius:20px;padding:32px 26px;text-align:center;box-shadow:0 16px 50px rgba(0,0,0,.45)}
#lock .logo{width:56px;height:56px;border-radius:16px;margin:0 auto 16px;font-size:28px}
#lock h1{font-size:21px;font-weight:800;letter-spacing:-.5px}
#lock .tag{font-size:12px;color:#9a96b8;margin:4px 0 22px}
#lock input{text-align:center;font-size:15px;padding:13px}
#lock .err{color:#ff7a7a;font-size:12px;min-height:16px;margin-top:12px}
.lockbtn{cursor:pointer;user-select:none}
#confirm{position:fixed;inset:0;display:flex;align-items:center;justify-content:center;padding:24px;z-index:25;background:rgba(8,6,16,.72)}
#confirm .box{width:100%;max-width:360px;background:#1a1730;border:1px solid rgba(255,255,255,.1);border-radius:18px;padding:22px;box-shadow:0 18px 50px rgba(0,0,0,.5)}
#confirm h3{font-size:16px;font-weight:800;margin-bottom:6px}
#confirm .cfsub{font-size:12px;color:#9a96b8;margin-bottom:12px}
.cfrow{display:flex;justify-content:space-between;gap:12px;padding:9px 0;border-bottom:1px solid rgba(255,255,255,.06);font-size:13px}
.cfrow:last-child{border:0}.cfrow span{color:#9a96b8;white-space:nowrap}.cfrow b{text-align:right;word-break:break-all;font-family:ui-monospace,monospace}
#confirm .acts{display:flex;gap:10px;margin-top:16px}#confirm .acts .btn{flex:1;margin-top:0}
</style></head><body>
<div id="lock"><div class="box">
  <div class="logo">🛡️</div>
  <h1>Sequora</h1>
  <div class="tag">post-quantum wallet · enter your password to unlock</div>
  <div style="position:relative">
    <input id="lpw" type="password" placeholder="password" autocomplete="off" autocapitalize="off" autocorrect="off" spellcheck="false" onkeydown="if(event.key==='Enter')unlock()">
    <span id="eye" onclick="toggleEye()" style="position:absolute;right:12px;top:50%;transform:translateY(-50%);cursor:pointer;user-select:none;font-size:15px;opacity:.65" title="show / hide">👁</span>
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
</div></div>
<div class="app hide" id="app">
 <div class="top"><div class="brand"><div class="logo">🛡️</div>Sequora</div><div style="display:flex;gap:8px;align-items:center"><div class="net">● sequora-wasm</div><div class="net lockbtn" onclick="lock()">🔒 Lock</div></div></div>
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
   <div class="card"><h3>Staking rewards</h3><div class="asset"><div class="coin" style="background:linear-gradient(135deg,#3ddc97,#2bb673)">★</div><div><div class="nm"><span id="rew">0</span> SQR</div><div class="sub">pending across delegations</div></div></div></div>
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
function lock(){PW='';clearTimeout(idleTimer);$('app').classList.add('hide');$('lock').classList.remove('hide');$('lpw').value='';$('lcount').textContent='';$('lpw').focus()}
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
