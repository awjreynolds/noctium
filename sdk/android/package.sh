#!/usr/bin/env bash
set -euo pipefail

features=zkir-321
if [[ ${1:-} == --localnet ]]; then
  features+=,localnet
  shift
fi
if (( $# != 1 )); then
  echo "usage: bash sdk/android/package.sh [--localnet] NEW_ANDROID_AAR" >&2
  exit 2
fi
output=$1
if [[ -e "$output" || -L "$output" ]]; then
  echo "Android archive destination already exists: $output" >&2
  exit 1
fi

sdk="$(cd "$(dirname "$0")" && pwd)"
repo="$(cd "$sdk/../.." && pwd)"
ndk="$(cd "${ANDROID_NDK_HOME:?Set ANDROID_NDK_HOME to the installed Android NDK}" && pwd)"
platform="${ANDROID_SDK_ROOT:?Set ANDROID_SDK_ROOT to the installed Android SDK}/platforms/android-35/android.jar"
case "$(uname -s)" in
  Darwin) host=darwin-x86_64 ;;
  Linux) host=linux-x86_64 ;;
  *) echo "Unsupported Android build host" >&2; exit 2 ;;
esac
toolchain="$ndk/toolchains/llvm/prebuilt/$host/bin"
clang="$toolchain/aarch64-linux-android24-clang"

mkdir -p "$(dirname "$output")"
stage="$(mktemp -d "$(dirname "$output")/.noctium-android.XXXXXX")"
trap 'rm -rf "$stage"' EXIT
mkdir -p "$stage/aar/jni/arm64-v8a"
sources=("$sdk/WitnessSession.kt" "$sdk/NativeWitness.kt" "$sdk/LedgerSnapshot.kt")
cflags=()
if [[ $features == *,localnet ]]; then
  cflags+=(-DNOCTIUM_LOCALNET)
  sources+=("$sdk/DevelopmentTransaction.kt")
fi

archive="$(
  CC_aarch64_linux_android="$clang" AR_aarch64_linux_android="$toolchain/llvm-ar" \
    CARGO_TARGET_AARCH64_LINUX_ANDROID_LINKER="$clang" \
    cargo +1.100.0 build --locked --lib --manifest-path "$repo/runtime/Cargo.toml" \
      --no-default-features --features "$features" --target aarch64-linux-android \
      --message-format=json-render-diagnostics |
    python3 -c '
import json
import sys

archive = None
for line in sys.stdin:
    item = json.loads(line)
    if item.get("reason") == "compiler-artifact" and item["target"]["name"] == "noctium_runtime":
        archive = next(path for path in item["filenames"] if path.endswith("/libnoctium_runtime.a"))
if archive is None:
    sys.exit("Cargo did not emit the Noctium static library")
print(archive)
'
)"

"$clang" -std=c11 -O2 -Wall -Wextra -Werror -fPIC -shared \
  "${cflags[@]}" -I "$repo/runtime/include" "$sdk/noctium_jni.c" "$archive" \
  -Wl,--gc-sections -Wl,--exclude-libs,ALL -Wl,-z,defs -Wl,-z,max-page-size=16384 \
  -Wl,-soname,libnoctium_jni.so -llog -ldl -lm \
  -o "$stage/aar/jni/arm64-v8a/libnoctium_jni.so"
"$toolchain/llvm-strip" --strip-debug "$stage/aar/jni/arm64-v8a/libnoctium_jni.so"
kotlinc "${sources[@]}" -jvm-target 1.8 \
  -classpath "$platform" -d "$stage/aar/classes.jar"
cat > "$stage/aar/AndroidManifest.xml" <<'EOF'
<manifest xmlns:android="http://schemas.android.com/apk/res/android" package="org.noctium.sdk">
  <uses-sdk android:minSdkVersion="24"/>
</manifest>
EOF
cat > "$stage/aar/proguard.txt" <<'EOF'
-keep class org.noctium.sdk.Native {
    native <methods>;
}
-keep class org.noctium.sdk.LocalnetBridge {
    native <methods>;
}
-keep class org.noctium.sdk.NoctiumFailure {
    <init>(int);
}
EOF
(cd "$stage/aar" && zip -q -r ../noctium.aar .)
ln "$stage/noctium.aar" "$output"
