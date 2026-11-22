# Public composed-call fixture

These files contain public data read from the development chain at block 30432. `transaction.bin` is the canonical native transaction from extrinsic 4, the last extrinsic in the block. `caller.state` and `callee.state` are the corresponding block-end public contract-state bytes.

The pinned receipt in `docs/development/independent-composition-receipt.json` records transaction ID `44da763bbde860dd6057062ee1a7e6e86f9c751ceede1a651bee2de31e7b8583`, intent ID `7335e29a2900ed4191e8d052d9ab0c88cfe970d759822c5e3ad6caec59c2c4d5`, caller state SHA-256 `d3c2f809b7c6a6fd56ad7e9e1ff5d1979e0f94a9cc30f1d63d3087ef63e09cbf`, and callee state SHA-256 `96c73b9b42978a0411a12a16846d5c1ae6fb5ac544472f0843c29e2e37493bc0`.

`tests/IndependentComposition.lean` names the ordered calls `claim` and `advance`. The Rust test derives the transaction and intent IDs, checks receipt identity and finality shape, and requires the exact caller and callee state bytes. The report supplies the block and extrinsic coordinates as trusted test inputs. The test does not verify contract proofs or independently establish RPC receipt truth.

The offline Rust test runs under the report's `midnight-ledger-9-zkir-3.2.1` profile. Its policy check binds the selected profile to the runtime build. Proof bytes stay opaque in this fixture check.
