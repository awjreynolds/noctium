# Historical composition artifact rebuild

This check rebuilt the plan and ZKIR artifacts used by the two recorded native
composition transactions. It did not generate verifier keys or proofs, and it
did not contact a node or deploy a contract.

## Inputs and source caveat

The 30432 receipt names compiler commit
`64dea51821051b7f64273eb698173c7ae6602a7a`, tree
`5ef7c4633115bd0d7e236fe5c13a211d5ad5eb79`. The 30556 receipt names compiler
commit `71b87c4b9dd1179acc115978d19b1600130184ec`, tree
`93a131a14dd53a94d94037b14d93ead2e03f9d97`.

Both were extracted with `git archive` into separate scratch trees. Each tree
started with no `.lake` cache. Builds ran with `LEAN_PATH`, `LEAN_SRC_PATH` and
`LAKE_PATH` unset. Both target profile files had SHA-256
`02b4242c2561232daea1d7d1d29bde68f3157eb9eed8cfb037254a0013f40093`.

The 64dea518 archive does not contain `tests/IndependentComposition.lean`.
For the 30432 rebuild, I copied this file from commit 71b87c4 into the clean
archive. Its SHA-256 is
`e1b8a43ac92d0e869a26f5836a350a7440b7ff6c31672b37453d27df87025d35`, matching
the source hash recorded in both receipts. The 30432 result therefore qualifies
the exact compiler commit with the receipt-pinned source bytes, not an
unmodified 64dea518 tree.

## Rebuild command

From the repository root, set the tree variables to empty directories and the
result variables to new output paths, then run:

```sh
mkdir -p "$TREE_30432" "$TREE_30556"
git archive 64dea51821051b7f64273eb698173c7ae6602a7a | tar -x -C "$TREE_30432"
git archive 71b87c4b9dd1179acc115978d19b1600130184ec | tar -x -C "$TREE_30556"
git show 71b87c4b9dd1179acc115978d19b1600130184ec:tests/IndependentComposition.lean \
  > "$TREE_30432/tests/IndependentComposition.lean"

(cd "$TREE_30432" && env -u LEAN_PATH -u LEAN_SRC_PATH -u LAKE_PATH \
  lake exe noctium compile tests/IndependentComposition.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --emit ledger --output "$RESULT_30432")
(cd "$TREE_30556" && env -u LEAN_PATH -u LEAN_SRC_PATH -u LAKE_PATH \
  lake exe noctium compile tests/IndependentComposition.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --emit ledger --output "$RESULT_30556")
```

Run the compile commands from their matching extracted trees. Keep each result
path fresh and outside its source archive.

The 30432 and 30556 runs each reported zero circuit relations and two native
entrypoint relations. Their `noctium.json` files set `deployable` to false,
mark both native relations unqualified, and list four artifacts with role
`ledger`. The metadata maps each Impact plan to its named ZKIR relation.

## Exact artifact hashes

The hashes below match the corresponding caller and callee hashes in both
`independent-composition-receipt.json` and `composition-transport-receipt.json`.
The complete output directories from the two compiler builds were byte-identical.

| Artifact | SHA-256 |
| --- | --- |
| `IndependentCaller.claim.impact.json` | `449add20ec83c81628404e07f29cc1f7367387bc46f92eef581b2edb139bbe1d` |
| `IndependentCaller.claim.zkir` | `a34ca6dfd66edf227ca6fa47e693c0f7211c5ffa95d1e7d4e07176857b1b5e2a` |
| `IndependentCallee.advance.impact.json` | `aa17a5cf71a06f54a6c0164b795601186b8cf693e1b4ff50c38afa3fae5f6de7` |
| `IndependentCallee.advance.zkir` | `60b1f448ad806bbeae706618acc943d5d5c8c208a9578217be527867823ef977` |

The JSON checks reused `strict_json_bytes` from
`scripts/proofs/check-private-claim-lowering.py`. They verified the profile and
artifact metadata, the exact four receipt-pinned hashes, both relation version
headers, and each plan-to-relation filename mapping.

## Negative controls

I changed `increment count by 1` to `increment count by 2` in a temporary copy
of the 30556 source. The caller plan and relation kept their expected hashes.
The callee plan changed from `aa17a5cf…e5f6de7` to
`ed5b6200…bb2e0a9`, and its relation changed from `60b1f448…823ef977` to
`c117c694…9b722902`. The source was restored after the build.

I also appended one newline byte to a copy of the caller relation. Strict JSON
parsing still succeeded, but its digest no longer matched the receipt pin. This
confirms the byte check rejects a semantically harmless file change.

The focused selection check accepts the pinned output directory and rejects a
wrong caller pair, crossed caller/callee relations, and an output copy missing
the callee relation:

```sh
python3 scripts/proofs/check-historical-composition-selection.py \
  build/experiments/469-selection-check/output
```

The command uses the existing strict JSON parser and hash helpers. It does not
build artifacts, generate keys or proofs, or contact a node.
