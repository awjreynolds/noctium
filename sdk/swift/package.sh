#!/usr/bin/env bash
set -euo pipefail

features=zkir-321
if [[ ${1:-} == --localnet ]]; then
  features+=,localnet
  shift
fi
if (( $# < 2 )); then
  echo "usage: bash sdk/swift/package.sh [--localnet] NEW_DIRECTORY RUST_TARGET [RUST_TARGET ...]" >&2
  exit 2
fi

sdk="$(cd "$(dirname "$0")" && pwd)"
repo="$(cd "$sdk/../.." && pwd)"
output=$1
shift
if [[ -e "$output" || -L "$output" ]]; then
  echo "Swift package destination already exists: $output" >&2
  exit 1
fi
mkdir -p "$(dirname "$output")"
stage="$(mktemp -d "$(dirname "$output")/.noctium-swift.XXXXXX")"
trap 'rm -rf "$stage"' EXIT
mkdir "$stage/headers" "$stage/package"
cp "$sdk/CNoctium.modulemap" "$stage/headers/module.modulemap"
cp "$repo/runtime/include/noctium_control.h" "$repo/runtime/include/noctium_native.h" "$stage/headers/"
cp "$sdk/Package.swift" "$repo/LICENSE" "$stage/package/"
cp -R "$sdk/Sources" "$sdk/Tests" "$stage/package/"
fixture_directory="$repo/tests/fixtures/native-collection-pages"
fixture_resources="$stage/package/Tests/NoctiumTests/Fixtures"
mkdir -p "$fixture_resources"
cp "$fixture_directory/manifest.json" "$fixture_directory/plan.impact.json" \
  "$fixture_directory/empty.state" "$fixture_directory/populated.state" "$fixture_resources/"
if [[ $features == *,localnet ]]; then
  sed -i '' 's/let localnet = false/let localnet = true/' "$stage/package/Package.swift"
fi

targets=()
for target in "$@"; do
  case "$target" in
    aarch64-apple-darwin|aarch64-apple-ios|aarch64-apple-ios-sim) ;;
    *) echo "unsupported Swift SDK target: $target" >&2; exit 2 ;;
  esac
  targets+=(--target "$target")
done
archives="$(
  MACOSX_DEPLOYMENT_TARGET=13.0 IPHONEOS_DEPLOYMENT_TARGET=16.0 \
    cargo +1.100.0 build --locked --lib --manifest-path "$repo/runtime/Cargo.toml" \
      --no-default-features --features "$features" "${targets[@]}" \
      --message-format=json-render-diagnostics |
    python3 -c '
import json
import sys

archives = []
for line in sys.stdin:
    item = json.loads(line)
    if item.get("reason") == "compiler-artifact" and item["target"]["name"] == "noctium_runtime":
        archives.extend(path for path in item["filenames"] if path.endswith("/libnoctium_runtime.a"))
if len(archives) != int(sys.argv[1]):
    sys.exit("Cargo did not emit one Noctium static library per requested target")
print("\n".join(archives))
' "$#"
)"
libraries=()
while IFS= read -r archive; do
  libraries+=(-library "$archive" -headers "$stage/headers")
done <<< "$archives"
xcodebuild -create-xcframework "${libraries[@]}" -output "$stage/package/CNoctium.xcframework"
mkdir "$output"
mv "$stage/package/"* "$output/"
