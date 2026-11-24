# Noctium source API versions

Noctium's Lean source API version is `0.1.0`. Use
`noctium_require_source_api "0.1.0"` for an exact requirement or supply a Lake
version range.

```lean
noctium_require_source_api ">=0.1.0, <0.2.0"
```

Requirements persist in compiled Lean module metadata. `noctium check` and
`noctium compile` validate requirements from the imported module closure before
reporting success or publishing artifacts. An incompatible imported requirement
identifies the module that declared it.

The source API version describes Noctium's Lean authoring surface. The CLI and
Lean toolchain report their versions through `noctium --version`. Use
`noctium_require_target` to constrain the selected Midnight profile.

## Compact 0.36.1 observation

The pinned compiler reports language version `0.28.0` and runtime version
`0.21.0`. Use the pinned Compact 0.36.1 executable.

```text
compactc --version
0.36.1 (7fa3a117c 2026-11-11)
compactc --language-version
0.28.0
compactc --runtime-version
0.21.0
```

`compactc --skip-zk source.compact output/` accepted exact `0.28`,
`>= 0.28`, `>= 0.27`, and `>= 0.27 && <= 0.29`. It rejected exact `0.27` and
`>= 0.29` with `language version 0.28.0 mismatch`; malformed and
four-component versions failed during pragma parsing. OR ranges such as
`>= 0.27 || >= 0.29` passed. Contradictory constraints such as
`>= 0.29 && <= 0.27` failed with a language-version mismatch. Repeated
compatible pragmas passed. A conflicting second pragma failed in the declaring
file. When a file imported an external module, a requirement in the module's
source was enforced. The compiler reported the imported file as the source of
a mismatch.

The Noctium check compares the emitted ZKIR with an exact requirement, a range
and no requirement. All three successful declarations emit the same relation.

[Compact version checks](../../tests/compact/language-version.sh) · [Noctium CLI checks](../../tests/source-api-requirement.sh)
