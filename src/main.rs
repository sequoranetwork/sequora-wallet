// Sequora wallet — Rust shared-core prototype.
// Generates a post-quantum ML-DSA-65 key, derives the chain's sqr1... address
// (SHA-256(pubkey)[:20] + bech32 "sqr" — identical to the Go chain), and queries
// a balance from the chain's REST API.

use std::env;
use std::fs;
use std::path::PathBuf;

use bech32::{ToBase32, Variant};
use fips204::ml_dsa_65;
use fips204::traits::SerDes;
use sha2::{Digest, Sha256};

const HRP: &str = "sqr";
const DENOM: &str = "usqr";

fn key_path() -> PathBuf {
    let home = env::var("HOME").unwrap_or_else(|_| ".".into());
    PathBuf::from(home).join(".sequora-wallet").join("key.json")
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
    let (pk, sk) = ml_dsa_65::try_keygen().expect("keygen failed");
    let pk_bytes = pk.into_bytes();
    let sk_bytes = sk.into_bytes();
    let addr = derive_address(&pk_bytes);

    let dir = key_path().parent().unwrap().to_path_buf();
    fs::create_dir_all(&dir).unwrap();
    let json = serde_json::json!({
        "scheme": "ML-DSA-65",
        "pubkey": hex::encode(pk_bytes),
        "privkey": hex::encode(sk_bytes),
        "address": addr,
    });
    fs::write(key_path(), serde_json::to_string_pretty(&json).unwrap()).unwrap();

    println!("New Sequora wallet (post-quantum, ML-DSA-65 / FIPS 204)");
    println!("  pubkey size : {} bytes", pk_bytes.len());
    println!("  privkey size: {} bytes", sk_bytes.len());
    println!("  address     : {}", addr);
    println!("  saved to    : {}", key_path().display());
    println!("\n(The 1952-byte quantum-proof pubkey is hidden behind the 20-byte address.)");
}

fn cmd_address() {
    println!("{}", derive_address(&load_pubkey()));
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

fn main() {
    let args: Vec<String> = env::args().collect();
    match args.get(1).map(String::as_str).unwrap_or("help") {
        "new" => cmd_new(),
        "address" => cmd_address(),
        "balance" => cmd_balance(args.get(2).map(String::as_str).unwrap_or("http://localhost:1317")),
        _ => {
            println!("Sequora wallet (Rust shared-core prototype)");
            println!("  sqrwallet new                 generate an ML-DSA-65 key + sqr1 address");
            println!("  sqrwallet address             print this wallet's address");
            println!("  sqrwallet balance [rest_url]  query balance (default http://localhost:1317)");
        }
    }
}
