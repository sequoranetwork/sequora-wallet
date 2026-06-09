# Security Policy

## Status

Sequora is an **experimental prototype**. It is **not audited** and there is **no
mainnet** — testnet tokens have no monetary value. Do not use it to hold real value.

## Reporting a vulnerability

**Please do not open public issues for security vulnerabilities.** Disclosing an
unpatched flaw publicly puts users at risk.

Instead, report privately:

- Email: **security@sequora.example** *(replace with a monitored address before launch)*
- Include: a description, affected component (chain / wallet / website), steps to
  reproduce, and impact. A suggested fix is welcome.

We will acknowledge your report, work on a fix, and coordinate disclosure with you.
Please give us reasonable time to patch and ship before any public disclosure
(coordinated/embargoed disclosure).

## Scope

In scope: the chain (`sequorad`), the wallet, and supporting tooling in these
repositories. Out of scope: third-party dependencies (report upstream), and
social-engineering or physical attacks.

## Bug bounty

There is no paid bug bounty yet. A bounty (and a professional audit) are planned
**before mainnet**. Until then, responsible disclosure is greatly appreciated and
will be credited.

## Known limitations

This is pre-audit software. Validator consensus keys are classical Ed25519 (a
post-quantum-consensus upgrade is planned for v2), and the software wallet cannot
protect against a fully compromised host. See the project docs for the current
threat model and operational hardening guidance.
