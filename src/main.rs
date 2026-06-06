// Sequora wallet — Rust shared-core prototype.
// Generates a post-quantum ML-DSA-65 key, derives the chain's sqr1... address
// (SHA-256(pubkey)[:20] + bech32 "sqr" — identical to the Go chain), and queries
// a balance from the chain's REST API.

use std::env;
use std::fs;
use std::io::Read;
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

fn load_keypair(pw: &str) -> (Vec<u8>, ml_dsa_65::PrivateKey) {
    let data = fs::read_to_string(key_path()).expect("no wallet — run `sqrwallet new`");
    let v: serde_json::Value = serde_json::from_str(&data).expect("corrupt key file");
    let pubkey = hex::decode(v["pubkey"].as_str().unwrap()).unwrap();
    let enc = &v["enc"];
    let salt = hex::decode(enc["salt"].as_str().expect("salt")).unwrap();
    let nonce = hex::decode(enc["nonce"].as_str().expect("nonce")).unwrap();
    let ct = hex::decode(enc["ciphertext"].as_str().expect("ciphertext")).unwrap();
    let key = derive_key(pw, &salt);
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
    match ureq::get(&url).call() {
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
    let vals = rest_get(rest, "/cosmos/staking/v1beta1/validators?pagination.limit=100");
    let validators: Vec<serde_json::Value> = vals["validators"]
        .as_array()
        .cloned()
        .unwrap_or_default()
        .iter()
        .map(|v| serde_json::json!({"moniker": v["description"]["moniker"], "valoper": v["operator_address"], "tokens": v["tokens"]}))
        .collect();
    let dels = rest_get(rest, &format!("/cosmos/staking/v1beta1/delegations/{addr}"));
    let delegations: Vec<serde_json::Value> = dels["delegation_responses"]
        .as_array()
        .cloned()
        .unwrap_or_default()
        .iter()
        .map(|d| serde_json::json!({"valoper": d["delegation"]["validator_address"], "amount": d["balance"]["amount"]}))
        .collect();
    serde_json::json!({"address": addr, "balance": balance, "validators": validators, "delegations": delegations}).to_string()
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
        _ => return (400, "application/json", "{\"error\":\"unknown action\"}".into()),
    };
    match broadcast_msg(rest, chain_id, any, gas, fee, &pw) {
        Ok((code, txhash, log)) => (200, "application/json", serde_json::json!({"code": code, "txhash": txhash, "log": log}).to_string()),
        Err(e) => (200, "application/json", serde_json::json!({"error": e}).to_string()),
    }
}

fn route(method: &tiny_http::Method, url: &str, body: &str, chain_id: &str, rest: &str) -> (u16, &'static str, String) {
    match (method, url) {
        (tiny_http::Method::Get, "/") => (200, "text/html", DASHBOARD_HTML.to_string()),
        (tiny_http::Method::Get, "/api/info") => (200, "application/json", info_json(rest)),
        (tiny_http::Method::Post, "/api/send") => api_action(body, rest, chain_id, "send"),
        (tiny_http::Method::Post, "/api/stake") => api_action(body, rest, chain_id, "stake"),
        (tiny_http::Method::Post, "/api/claim") => api_action(body, rest, chain_id, "claim"),
        _ => (404, "text/plain", "not found".into()),
    }
}

fn cmd_serve(port: u16, chain_id: &str, rest: &str) {
    let bind = format!("0.0.0.0:{port}");
    let server = tiny_http::Server::http(&bind).expect("bind");
    println!("Sequora wallet UI running:");
    println!("  open  http://localhost:{port}  in your browser");
    println!("  chain {chain_id} via {rest}");
    for mut req in server.incoming_requests() {
        let method = req.method().clone();
        let url = req.url().to_string();
        let mut body = String::new();
        if method == tiny_http::Method::Post {
            let _ = req.as_reader().read_to_string(&mut body);
        }
        let (status, ctype, out) = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            route(&method, &url, &body, chain_id, rest)
        }))
        .unwrap_or((500, "application/json", "{\"error\":\"wrong password or internal error\"}".to_string()));
        let header = tiny_http::Header::from_bytes(&b"Content-Type"[..], ctype.as_bytes()).unwrap();
        let _ = req.respond(tiny_http::Response::from_string(out).with_status_code(status).with_header(header));
    }
}

const DASHBOARD_HTML: &str = r##"<!doctype html><html><head><meta charset="utf-8"><title>Sequora Wallet</title>
<style>
 body{font-family:system-ui,sans-serif;max-width:760px;margin:24px auto;padding:0 16px;background:#0d1117;color:#e6edf3}
 h1{font-size:22px} h2{font-size:15px;color:#7ee787;margin-top:24px;border-bottom:1px solid #30363d;padding-bottom:4px}
 .card{background:#161b22;border:1px solid #30363d;border-radius:8px;padding:14px;margin:10px 0}
 .addr{font-family:monospace;font-size:12px;word-break:break-all;color:#58a6ff}
 .bal{font-size:28px;font-weight:700}
 input{background:#0d1117;color:#e6edf3;border:1px solid #30363d;border-radius:6px;padding:6px;margin:2px}
 button{background:#238636;color:#fff;border:0;border-radius:6px;padding:7px 12px;cursor:pointer;font-weight:600}
 button:hover{background:#2ea043} .row{display:flex;gap:6px;align-items:center;flex-wrap:wrap;margin:4px 0}
 .muted{color:#8b949e;font-size:12px} #out{white-space:pre-wrap;font-family:monospace;font-size:12px;color:#d29922}
 .pill{background:#21262d;border-radius:20px;padding:2px 8px;font-size:11px;color:#8b949e}
</style></head><body>
<h1>🛡️ Sequora Wallet <span class="pill">post-quantum · ML-DSA-65</span></h1>
<div class="card">
  <div class="muted">your address</div>
  <div class="addr" id="addr">…</div>
  <div class="bal"><span id="bal">…</span> <span class="muted" style="font-size:14px">SQR</span></div>
</div>
<div class="card">
  <div class="muted">password (to sign — unlocks your encrypted key)</div>
  <input id="pw" type="password" placeholder="wallet password" style="width:280px">
</div>
<h2>Send</h2>
<div class="card"><div class="row">
  <input id="sendTo" placeholder="sqr1… recipient" style="width:320px">
  <input id="sendAmt" placeholder="amount (usqr)" style="width:140px">
  <button onclick="send()">Send</button>
</div></div>
<h2>Stake to a validator</h2>
<div class="card" id="vals">…</div>
<h2>Your delegations</h2>
<div class="card" id="dels">…</div>
<h2>Result</h2>
<div class="card"><div id="out">—</div></div>
<script>
function pw(){return document.getElementById('pw').value}
function show(o){document.getElementById('out').textContent=JSON.stringify(o,null,2)}
async function refresh(){
  let r=await fetch('/api/info'); let d=await r.json();
  document.getElementById('addr').textContent=d.address;
  document.getElementById('bal').textContent=(parseInt(d.balance||0)/1e6).toLocaleString();
  let vh=d.validators.map(v=>`<div class="row"><b>${v.moniker}</b> <span class="muted">${(v.tokens/1e6).toLocaleString()} SQR</span>
    <input id="amt_${v.valoper}" placeholder="usqr" style="width:120px">
    <button onclick="stake('${v.valoper}')">Stake</button></div>`).join('')||'<span class="muted">none</span>';
  document.getElementById('vals').innerHTML=vh;
  let dh=d.delegations.map(x=>`<div class="row"><span class="muted">${x.valoper.slice(0,24)}…</span> <b>${(x.amount/1e6).toLocaleString()} SQR</b>
    <button onclick="claim('${x.valoper}')">Claim rewards</button></div>`).join('')||'<span class="muted">none yet</span>';
  document.getElementById('dels').innerHTML=dh;
}
async function post(path,obj){obj.password=pw(); let r=await fetch(path,{method:'POST',body:JSON.stringify(obj)}); let d=await r.json(); show(d); setTimeout(refresh,3000); return d}
function send(){post('/api/send',{to:document.getElementById('sendTo').value,amount:document.getElementById('sendAmt').value})}
function stake(v){post('/api/stake',{valoper:v,amount:document.getElementById('amt_'+v).value})}
function claim(v){post('/api/claim',{valoper:v})}
refresh();
</script></body></html>"##;

fn main() {
    let args: Vec<String> = env::args().collect();
    match args.get(1).map(String::as_str).unwrap_or("help") {
        "new" => cmd_new(),
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
            println!("  sqrwallet new                 generate an ML-DSA-65 key + sqr1 address");
            println!("  sqrwallet address             print this wallet's address");
            println!("  sqrwallet balance [rest_url]  query balance (default http://localhost:1317)");
        }
    }
}
