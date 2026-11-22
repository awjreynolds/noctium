# Host CAS cases

`cases.json` is the shared synthetic input for the Lean host-CAS model check and the Rust public-ABI acceptance test. Its attempt and transaction IDs are dummy values. The journal digest is a redacted marker because the Rust test binds each response to the digest returned by its live private journal. The model and runtime test check digest equality only. They do not establish digest authenticity, storage durability, or receipt truth.
