# Source proof report performance

Run the benchmark manually when the report or audit driver changes. It runs two fresh report processes, requires byte-identical JSON and model/proof exports, then replays the retained exports in a fresh data-only process. It uses the existing `.lake` cache. Each report timing includes the checker's build step and source export work.

```sh
python3 scripts/proofs/benchmark-source-report.py \
  --output-dir build/experiments/source-proof-performance-2026-11-22
```

The first measurement on compiler base `932a6da3612b9407ffc9f7f03316dc6662fb810b` ran on Apple ARM64 macOS with Lean and Lake 4.35.0. It used target profile `midnight-ledger-9-zkir-3.2.1` and the working tree changes to the report checker and benchmark script, before commit. The report runs took 49.116 and 49.618 seconds. Data-only replay took 27.763 seconds. Both reports were 3,504 bytes with SHA256 `81ff0c407cf42bdd613f2c00f8e1d429a071c09bb2d12ae09b5df890b8308f02`. Each model export was 26,235,862 bytes with SHA256 equal to its checked-in pin, `5d731c6cd846c9896ac0f59040946a510536816e1a468cf4e4075812a8514a5c`. Each proof export was 45,472,463 bytes with SHA256 `624867a3779353b7db92c8199365ee569f8493b0d0301d8aec7396ce8d4695e3`.

The repeat on compiler base `2429ed8f449f911b01a23499be8a26009ebe5174` took 54.270 and 50.477 seconds for the reports and 28.967 seconds for data-only replay. The report, model and proof sizes and hashes matched the first measurement. Both measurements used the audit driver at SHA-256 `40714f5703e2e473710bc9f304b014d4813e35363416d41cfd5aac54be697d32` and the benchmark script at `13de14fe4233c8a8ac1e799c08abb23e032ed66e95df939eec3b8bc6f8848d76`.

`benchmark.json` records input hashes and timings. The measured operation is `PrivateClaim.claim` with both registered functional and scoped privacy checks. Proposed warm-cache targets for this host are 60 seconds per report, 35 seconds per data-only replay, 8 KiB for report JSON, 32 MiB for the model export and 56 MiB for the proof export.

In GitHub Actions, choose **Source assurance replay** to run the pinned PrivateClaim and BoundedScalars reports on demand. Use the local command above for measurements.
