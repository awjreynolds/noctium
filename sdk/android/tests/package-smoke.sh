#!/usr/bin/env bash
set -euo pipefail

localnet=false
collection_pages=false
if [[ ${1:-} == --collection-pages ]]; then
  collection_pages=true
  shift
fi
if [[ ${1:-} == --localnet ]]; then
  localnet=true
  shift
fi

if "$collection_pages" && "$localnet"; then
  echo "--collection-pages cannot be combined with --localnet" >&2
  exit 2
fi
if "$collection_pages"; then
  if (( $# != 2 )); then
    echo "usage: bash sdk/android/tests/package-smoke.sh --collection-pages AAR NEW_APK" >&2
    exit 2
  fi
elif (( $# < 3 || $# > 4 )) || { "$localnet" && (( $# != 4 )); }; then
  echo "usage: bash sdk/android/tests/package-smoke.sh [--localnet] AAR HOST_CONTROL_PLAN NEW_APK [PUBLIC_PROOF_FIXTURE]" >&2
  exit 2
fi
sdk="$(cd "$(dirname "$0")" && pwd)"
repo="$(cd "$sdk/../../.." && pwd)"
android="${ANDROID_SDK_ROOT:?Set ANDROID_SDK_ROOT to the installed Android SDK}"
tool_version="${ANDROID_BUILD_TOOLS_VERSION:-35.0.0}"
tool="$android/build-tools/$tool_version"
platform="$android/platforms/android-35/android.jar"
if "$collection_pages"; then
  output=$2
else
  output=$3
fi
if [[ -e "$output" || -L "$output" ]]; then
  echo "Android smoke APK destination already exists: $output" >&2
  exit 1
fi
mkdir -p "$(dirname "$output")"
stage="$(mktemp -d "$(dirname "$output")/.noctium-android-smoke.XXXXXX")"
trap 'rm -rf "$stage"' EXIT
mkdir -p "$stage/assets" "$stage/aar" "$stage/native/lib/arm64-v8a" "$stage/dex"
unzip -q "$1" -d "$stage/aar"
if "$collection_pages"; then
  fixture="$repo/tests/fixtures/native-collection-pages"
  mkdir "$stage/assets/native-collection-pages"
  cp "$fixture/manifest.json" "$fixture/plan.impact.json" \
    "$fixture/empty.state" "$fixture/populated.state" "$stage/assets/native-collection-pages/"
  sources=("$sdk/CollectionPagesSmoke.kt")
  instrumentation=.CollectionPagesSmoke
else
  cp "$2" "$stage/assets/plan.json"
  if (( $# == 4 )); then
    mkdir "$stage/assets/proof"
    cp "$4/target.json" "$4/srs" "$stage/assets/proof/"
    cp -R "$4/bundle" "$stage/assets/proof/bundle"
  fi
  sources=("$sdk/WitnessSmoke.kt")
  instrumentation=.WitnessSmoke
fi
permission=
app_settings=
if "$localnet"; then
  mkdir "$stage/assets/proof/localnet"
  cp "$4/localnet/client.json" "$4/localnet/localnet.json" "$stage/assets/proof/localnet/"
  cp -R "$4/localnet/params" "$stage/assets/proof/localnet/params"
  if [[ -f "$4/synthetic-claim.json" ]]; then
    cp "$4/synthetic-claim.json" "$stage/assets/proof/"
  fi
  sources+=("$sdk/DevelopmentSmoke.kt")
  instrumentation=.DevelopmentSmoke
  permission='<uses-permission android:name="android.permission.INTERNET"/>'
  app_settings='android:usesCleartextTraffic="true"'
fi
cp "$stage/aar/jni/arm64-v8a/libnoctium_jni.so" "$stage/native/lib/arm64-v8a/"
cat > "$stage/AndroidManifest.xml" <<EOF
<manifest xmlns:android="http://schemas.android.com/apk/res/android" package="org.noctium.sdk.tests">
  <uses-sdk android:minSdkVersion="24" android:targetSdkVersion="35"/>
  $permission
  <application android:extractNativeLibs="true" android:label="Noctium Android smoke test" $app_settings/>
  <instrumentation android:name="$instrumentation" android:targetPackage="org.noctium.sdk.tests"/>
</manifest>
EOF
kotlinc "${sources[@]}" -jvm-target 1.8 -classpath "$platform:$stage/aar/classes.jar" \
    -d "$stage/smoke.jar"
"$tool/d8" --min-api 24 --lib "$platform" --output "$stage/dex" \
    "$stage/smoke.jar" "$stage/aar/classes.jar" "${KOTLIN_HOME:?Set KOTLIN_HOME}/lib/kotlin-stdlib.jar"
"$tool/aapt2" link -I "$platform" --manifest "$stage/AndroidManifest.xml" -A "$stage/assets" -o "$stage/smoke.apk"
(cd "$stage/dex" && zip -q ../smoke.apk classes*.dex)
(cd "$stage/native" && zip -q -r ../smoke.apk lib)
"$tool/zipalign" -f 4 "$stage/smoke.apk" "$stage/aligned.apk"
keytool -genkeypair -keystore "$stage/smoke.p12" -storepass changeit -keypass changeit -alias smoke \
    -dname CN=NoctiumTest -keyalg RSA -validity 1 >/dev/null 2>&1
"$tool/apksigner" sign --ks "$stage/smoke.p12" --ks-pass pass:changeit --out "$stage/signed.apk" "$stage/aligned.apk"
ln "$stage/signed.apk" "$output"
