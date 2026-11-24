#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../.."
compiler=${1:-compactc}
case "$("$compiler" --version)" in
  '0.36.1 (7fa3a117c '*) ;;
  *) echo 'expected pinned Compact 0.36.1 (7fa3a117c)' >&2; exit 1 ;;
esac
test "$("$compiler" --language-version)" = 0.28.0
test "$("$compiler" --runtime-version)" = 0.21.0

mkdir -p build/experiments
scratch=$(mktemp -d "$PWD/build/experiments/compact-language-version.XXXXXX")
trap 'rm -rf "$scratch"' EXIT

write_circuit() {
  printf '%s\n' "$1" 'export circuit value(): Field { return (7 as Field); }' > "$scratch/Main.compact"
}

compile() {
  "$compiler" --skip-zk "$scratch/Main.compact" "$scratch/$1" > "$scratch/compiler.log" 2>&1
}

reject() {
  if compile "$1"; then
    echo "Compact version case $1 unexpectedly compiled" >&2
    exit 1
  fi
  grep -F "$2" "$scratch/compiler.log" > /dev/null
}

write_circuit 'pragma language_version 0.28;'
compile exact
write_circuit 'pragma language_version >= 0.27 && <= 0.29;'
compile bounded
write_circuit 'pragma language_version >= 0.27 || >= 0.29;'
compile either
write_circuit $'pragma language_version 0.28;\npragma language_version >= 0.29;'
reject conflicting 'language version 0.28.0 mismatch'
write_circuit 'pragma language_version 0.27;'
reject old 'language version 0.28.0 mismatch'

cat > "$scratch/Main.compact" <<'COMPACT'
pragma language_version 0.28;
import Inner;
export { value };
COMPACT
cat > "$scratch/Inner.compact" <<'COMPACT'
pragma language_version >= 0.28;
module Inner {
  export circuit value(): Field { return (7 as Field); }
}
COMPACT
compile matching_import
sed 's/>= 0.28/>= 0.29/' "$scratch/Inner.compact" > "$scratch/updated.compact"
mv "$scratch/updated.compact" "$scratch/Inner.compact"
reject incompatible_import 'language version 0.28.0 mismatch'
grep -F 'Inner.compact' "$scratch/compiler.log" > /dev/null
