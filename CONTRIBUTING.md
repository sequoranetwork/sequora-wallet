# Contributing to Seaqoin

Thanks for your interest! Seaqoin is an open, community-oriented project — a
quantum-resistant Layer 1 (chain), a secure wallet, and a website. Contributions
of all kinds are welcome.

## Ground rules

- **Be respectful.** Assume good faith; keep discussion technical.
- **Security issues** go through [`SECURITY.md`](SECURITY.md) — **not** public
  issues or PRs.
- By contributing, you agree your contributions are licensed under the project's
  **Apache License 2.0** (see [`LICENSE`](LICENSE)).

## How to contribute

1. Open an issue to discuss non-trivial changes first.
2. Fork, create a branch, make focused commits.
3. Ensure it builds and tests pass (see below).
4. Open a pull request describing the change and why.

## Build & test

- **Chain** (Go): `make install` to build `sequorad`; `make test` (govet +
  govulncheck + unit tests). New logic should come with tests.
- **Wallet** (Rust): `cargo build --release`; `cargo test`; `cargo audit`.
- **Website**: static — open `index.html`, or `python3 -m http.server`.

## Style

- Match the surrounding code's conventions, naming, and comment density.
- Keep changes minimal and well-scoped; explain non-obvious decisions in comments.
- No secrets, keys, or credentials in commits.

## Sign-off (optional but encouraged)

Use `git commit -s` to add a Developer Certificate of Origin sign-off.
