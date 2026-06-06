// Sequora wallet — Rust shared-core prototype.
// Generates a post-quantum ML-DSA-65 key, derives the chain's sqr1... address
// (SHA-256(pubkey)[:20] + bech32 "sqr" — identical to the Go chain), and queries
// a balance from the chain's REST API.

use std::env;
use std::fs;
use std::path::PathBuf;

use bech32::{ToBase32, Variant};
use fips204::ml_dsa_65;
use fips204::traits::{SerDes, Signer};
use sha2::{Digest, Sha256};

use argon2::Argon2;
use base64::Engine;
use chacha20poly1305::aead::Aead;
use chacha20poly1305::{ChaCha20Poly1305, KeyInit, Nonce};
use cosmos_sdk_proto::cosmos::bank::v1beta1::MsgSend;
use cosmos_sdk_proto::cosmos::base::v1beta1::Coin;
use cosmos_sdk_proto::cosmos::distribution::v1beta1::MsgWithdrawDelegatorReward;
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
    env::var("SQRWALLET_PASSWORD")
        .expect("set SQRWALLET_PASSWORD to unlock the wallet (a real wallet would prompt securely / use the OS keychain)")
}

fn rand_bytes(n: usize) -> Vec<u8> {
    let mut b = vec![0u8; n];
    getrandom::getrandom(&mut b).expect("rng");
    b
}

fn derive_key(password: &str, salt: &[u8]) -> [u8; 32] {
    let mut key = [0u8; 32];
    Argon2::default()
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

fn load_pubkey() -> Vec<u8> {
    let data = fs::read_to_string(key_path()).expect("no wallet found — run `sqrwallet new` first");
    let v: serde_json::Value = serde_json::from_str(&data).expect("corrupt key file");
    hex::decode(v["pubkey"].as_str().expect("missing pubkey")).expect("bad hex")
}

fn cmd_new() {
    let password = get_password();
    let (pk, sk) = ml_dsa_65::try_keygen().expect("keygen failed");
    let pk_bytes = pk.into_bytes();
    let sk_bytes = sk.into_bytes();
    let addr = derive_address(&pk_bytes);

    // encrypt the private key at rest
    let salt = rand_bytes(16);
    let nonce = rand_bytes(12);
    let key = derive_key(&password, &salt);
    let cipher = ChaCha20Poly1305::new_from_slice(&key).expect("cipher");
    let ciphertext = cipher
        .encrypt(Nonce::from_slice(&nonce), sk_bytes.as_ref())
        .expect("encrypt");

    let dir = key_path().parent().unwrap().to_path_buf();
    fs::create_dir_all(&dir).unwrap();
    let json = serde_json::json!({
        "scheme": "ML-DSA-65",
        "pubkey": hex::encode(pk_bytes),
        "address": addr,
        "enc": {
            "kdf": "argon2id",
            "cipher": "chacha20poly1305",
            "salt": hex::encode(&salt),
            "nonce": hex::encode(&nonce),
            "ciphertext": hex::encode(&ciphertext),
        }
    });
    fs::write(key_path(), serde_json::to_string_pretty(&json).unwrap()).unwrap();

    println!("New ENCRYPTED Sequora wallet (post-quantum, ML-DSA-65 / FIPS 204)");
    println!("  pubkey size : {} bytes", pk_bytes.len());
    println!("  address     : {}", addr);
    println!("  key at rest : Argon2id + ChaCha20-Poly1305 — private key NEVER stored in plaintext");
    println!("  saved to    : {}", key_path().display());
}

fn cmd_address() {
    println!("{}", derive_address(&load_pubkey()));
}

// cmd_sign signs a message with the wallet's ML-DSA-65 key and prints the
// pubkey/message/signature as hex — so the chain (MsgVerifyPqc) can verify it,
// proving Rust(fips204) <-> Go(circl) signature interop.
fn cmd_sign(message: &str) {
    let (pubkey, sk) = load_keypair(); // decrypts with SQRWALLET_PASSWORD
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
    match ureq::get(&url).call() {
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

fn load_keypair() -> (Vec<u8>, ml_dsa_65::PrivateKey) {
    let data = fs::read_to_string(key_path()).expect("no wallet — run `sqrwallet new`");
    let v: serde_json::Value = serde_json::from_str(&data).expect("corrupt key file");
    let pubkey = hex::decode(v["pubkey"].as_str().unwrap()).unwrap();
    let enc = &v["enc"];
    let salt = hex::decode(enc["salt"].as_str().expect("salt")).unwrap();
    let nonce = hex::decode(enc["nonce"].as_str().expect("nonce")).unwrap();
    let ct = hex::decode(enc["ciphertext"].as_str().expect("ciphertext")).unwrap();
    let key = derive_key(&get_password(), &salt);
    let cipher = ChaCha20Poly1305::new_from_slice(&key).expect("cipher");
    let sk_vec = cipher
        .decrypt(Nonce::from_slice(&nonce), ct.as_ref())
        .expect("decrypt failed — wrong password?");
    let sk_arr: [u8; ml_dsa_65::SK_LEN] = sk_vec.try_into().expect("bad privkey length");
    let sk = ml_dsa_65::PrivateKey::try_from_bytes(sk_arr).expect("load privkey");
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

// Builds a SIGN_MODE_DIRECT tx around `msg`, signs the SignDoc with ML-DSA-65,
// and broadcasts via the chain REST endpoint.
fn sign_and_broadcast(rest: &str, chain_id: &str, msg: Any, gas: u64, fee_usqr: u64) {
    let (pubkey, sk) = load_keypair();
    let from = derive_address(&pubkey);
    let (acct_num, seq) = query_account(rest, &from);
    println!("  signer {from}  acct#={acct_num} seq={seq}");

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
    let sig = sk.try_sign(&sign_doc.encode_to_vec(), &[]).expect("sign");
    println!("  ML-DSA-65 signature: {} bytes", sig.len());

    let tx_raw = TxRaw {
        body_bytes,
        auth_info_bytes,
        signatures: vec![sig.to_vec()],
    };
    let tx_b64 = base64::engine::general_purpose::STANDARD.encode(tx_raw.encode_to_vec());

    let url = format!("{}/cosmos/tx/v1beta1/txs", rest.trim_end_matches('/'));
    match ureq::post(&url).send_json(serde_json::json!({"tx_bytes": tx_b64, "mode": "BROADCAST_MODE_SYNC"})) {
        Ok(r) => {
            let v: serde_json::Value =
                serde_json::from_str(&r.into_string().unwrap_or_default()).unwrap_or(serde_json::json!({}));
            let tr = &v["tx_response"];
            println!("  broadcast code={} txhash={}", tr["code"], tr["txhash"].as_str().unwrap_or("?"));
            let log = tr["raw_log"].as_str().unwrap_or("");
            if !log.is_empty() {
                println!("  raw_log: {log}");
            }
        }
        Err(e) => println!("  broadcast failed: {e}"),
    }
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

fn main() {
    let args: Vec<String> = env::args().collect();
    match args.get(1).map(String::as_str).unwrap_or("help") {
        "new" => cmd_new(),
        "address" => cmd_address(),
        "balance" => cmd_balance(args.get(2).map(String::as_str).unwrap_or("http://localhost:1317")),
        "sign" => cmd_sign(args.get(2).map(String::as_str).unwrap_or("hello-sequora")),
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
            println!("  sqrwallet new                 generate an ML-DSA-65 key + sqr1 address");
            println!("  sqrwallet address             print this wallet's address");
            println!("  sqrwallet balance [rest_url]  query balance (default http://localhost:1317)");
        }
    }
}
