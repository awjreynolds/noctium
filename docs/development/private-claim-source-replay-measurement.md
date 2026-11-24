# PrivateClaim source replay measurement

Run this from the repository root with Lean 4.35.0, Lake, Python 3, and the existing `.lake` cache:

```sh
python3 scripts/proofs/measure-private-claim-source-replay.py
```

The command writes one JSON result to stdout. It compares two fresh source reports, model exports, proof exports, and audit results byte-for-byte. It times the dependency build, standalone source compilation and coverage, the first source-report generation, and a fresh data-only replay. The source-report command runs its own dependency build, source compilation, export generation, source-coverage and artifact checks, and proof audit. The same source-report command runs a second time to confirm byte equality, but only the first invocation contributes a source-report-generation time. The replay uses the retained exports and excludes source compilation and export generation.

The helper creates temporary reports and exports under `build/experiments/` and removes them on exit. Redirect stdout to retain the small measurement record. The deterministic evidence digest covers report and export identities, not timings.

## Captured warm-cache sample

The sample ran on macOS 26.6.2 arm64 with Lean 4.35.0 and Lake 5.0.0, at revision `e1bc5935d94d9c91049c944056be142273031058`. The worktree was dirty. The measured helper SHA-256 was `869d5e6519294a91ba2d66ac1a9ce41221cbe9417d79fe5ca2c5a1aa1c4f0323`.

| Measurement | Sample | Performance target | Safety ceiling |
| --- | ---: | ---: | ---: |
| Dependency build | 0.433947 s | 10 s | 300 s |
| Source compilation and coverage | 8.067909 s | 12 s | 240 s |
| First source report generation | 77.655593 s | 120 s | 900 s |
| Data-only replay | 30.314429 s | 35 s | 180 s |
| Source report JSON | 6,539 bytes | 8,192 bytes | 65,536 bytes |
| Audit JSON | 16,686 bytes | 20,480 bytes | 65,536 bytes |
| Trusted model export | 33,148,293 bytes | 33,554,432 bytes | 67,108,864 bytes |
| Proof export | 46,622,538 bytes | 58,720,256 bytes | 67,108,864 bytes |

The deterministic evidence digest was `2260de3cd423edf1003aa58906ba95986c0635d3d01a94a488293aac9c9607fd`. The model export matched fixture pin `2100fcefc77e4f7313c47097e0cdc94c8307d7d25eecffa98cc9591f3730e369`. All four timing targets and four size targets passed.

Performance targets describe this warm-cache host. A target miss appears in `targetStatus` and does not fail the measurement. Safety ceilings bound command time and artifact size. A ceiling breach, mismatched repeated report or rejected data-only replay stops the run before the helper prints a success record.
