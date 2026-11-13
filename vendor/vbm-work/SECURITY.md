# Security policy

vbm-work is a **pre-release** library. Nothing is published to a package registry and there are no supported versions yet; report problems against the latest `main`.

## What to report

- A hole in the proofs: a way to make a theorem claim more than it says (a forbidden construct that evades the gates, an axiom, a theorem about code that does not run).
- A patch sequence or compaction that drops the goal, an obligation or a pinned fact, or a state that exceeds the stated size bound.
- A crash, hang or unbounded memory use on any input.
- A way to land a change without passing Tier 1, or any secret, credential or key committed to the repository.

The library is pure data and functions: it does not talk to a network, hold a credential or call a model, so no key or token belongs in this repository, its tests or its logs.

## How to report

Use GitHub's private vulnerability reporting for this repository (Security tab, "Report a vulnerability"). If that is not available, open an issue that says only that you have a security report and ask for a private channel; do not put exploit details in a public issue.

Please include the input (or a minimal one), the commit and what you expected.

## What to expect

This is maintained on a best-effort basis. Expect an acknowledgement within about a week and a fix or a written assessment as soon as practical. A confirmed bug is fixed on `main` with a regression scenario.
