# Kotlin witness SDK for Android

The Kotlin SDK runs Noctium host-control plans and generates and verifies proofs on Android through the shared Rust runtime. The Android archive links one arm64-v8a native library and needs no Node process. Use a worker thread for witness execution and local proving.

## Build and import

Install Rust 1.100.0, JDK 21, Kotlin, CMake, Android SDK Platform 35 and the Android NDK. Set `ANDROID_SDK_ROOT` and `ANDROID_NDK_HOME` to their installation directories. Put `cargo`, `kotlinc`, `python3` and `zip` on your path.

```sh
rustup target add --toolchain 1.100.0 aarch64-linux-android
bash sdk/android/package.sh build/noctium-android.aar
```

Add the AAR to your Android application and link the Kotlin standard library. The archive targets API 24 and newer on arm64 and includes the keep rules for its JNI entrypoints. The build uses the locked ZKIR 3.2.1 Rust runtime and aligns native ELF segments to 16 KiB. [Android NDK build guide](https://developer.android.com/ndk/guides/other_build_systems) · [Android page-size requirements](https://developer.android.com/guide/practices/page-sizes)

## Run a witness

Compile your `noctium_control` declaration with `--emit control`. Pass the emitted plan, invocation inputs and host capability registrations in the Control ABI's UTF-8 begin envelope.

```kotlin
import org.noctium.sdk.WitnessSession

WitnessSession.open(beginEnvelope).use { session ->
    val step = session.advance()
    // Inspect the private host step and dispatch any registered callback.
}
```

On `need_host`, retrieve the separate private request with `privateRequest()`. Pass the exact correlated JSON reply to `resume()` and advance again. Use `typed = false` for a v1 reply. `cancel()` invalidates the pending callback, and `close()` frees the native invocation. `NoctiumFailure.status` carries the native error code. Keep step data, provider arguments and staged writes out of application logs. The app owns the copies it receives as byte arrays. [Control ABI](../../runtime/include/noctium_control.h)

## Prove a completed witness

Use `NativeWitness.open` for a ledger entrypoint. Provide the native target descriptor with the bundle directory's canonical path, the independently pinned manifest digest, the entrypoint and ledger parameters. Provide the exact bundled control plan, the initial state, the matching SRS bytes and the begin envelope containing the inputs and host context. [Target and proof descriptors](../../runtime/include/noctium_native.h)

```kotlin
import org.noctium.sdk.NativeWitness

NativeWitness.open(targetDescriptor, initialState, srs, controlPlan, beginEnvelope).use { invocation ->
    runCallbacksUntilCompleted(invocation.session)
    invocation.prepareProof(proofDescriptor).use { proof ->
        val publicIntent = proof.proveLocally()
    }
}
```

The application supplies `runCallbacksUntilCompleted`. Successful preparation consumes the target and witness. Proving retains the private preimage in the native runtime and returns the verified public intent projection.

For an entrypoint supplied with explicit inputs, use `NativeProof.open(descriptor, configuration, srs)`. The descriptor includes the bundle's canonical path, manifest and parameter digests, profile, K, TTL, proof capability and maximum response size. The private configuration contains the declared inputs and initial state. [Native proof descriptor](../../runtime/include/noctium_native.h)

## Read a ledger collection page

Pass the native ABI's UTF-8 page request, original Impact plan bytes and
tagged state snapshot to the Kotlin binding.

```kotlin
import org.noctium.sdk.LedgerSnapshot

val pageJson = LedgerSnapshot.collectionPage(request, impactPlan, taggedSnapshot)
```

Set `planSha256` and `stateSha256` from trusted metadata. For a root
List use an empty `keys` array and start at `offset: 0`. Follow the
returned `nextOffset` until the result returns `null`. The SDK returns an
owned UTF-8 JSON byte array and reports native failures through
`NoctiumFailure.status`. [Collection request and response format](../../runtime/include/noctium_native.h)

## Fund and submit on the development localnet

Build with `bash sdk/android/package.sh --localnet build/noctium-android-localnet.aar` to include the development adapter. The adapter authenticates the pinned development genesis and accepts a loopback endpoint. Use the native header's configuration, transaction descriptor and deployment setup. Supply a funded public development seed to fund a transaction. [Development stack](../../scripts/localnet/README.md) · [Native client interface](../../runtime/include/noctium_native.h)

```kotlin
import org.noctium.sdk.DevelopmentLocalnet
import org.noctium.sdk.DevelopmentTransaction.Command
import org.noctium.sdk.startDevelopmentCall

DevelopmentLocalnet(configuration, developmentSeed).use { adapter ->
    provedWitness.startDevelopmentCall(clientDescriptor).use { call ->
        drive(call, adapter, call.send(Command.PREPARE))
        storeRecoveryContext(call.recoveryContext())
        drive(call, adapter, call.send(Command.SUBMIT))
        observeUntilFinalized(call, adapter)
        drive(call, adapter, call.send(Command.COMMIT))
    }
}
```

The application supplies the driver, storage and finality loop. The driver passes each pending step to `resolve` and approves signing only after inspecting the request. The call takes ownership of the witness's staged private writes. Persist `recoveryContext()` in app-private storage before submitting. Keep the handle until the runtime acknowledges durable state and accepts `close()`. After a restart, open the same journal with `DevelopmentLocalnet(configuration)` and recover with `DevelopmentTransaction.recover(clientDescriptor, context)`. Remove the funding cache, source and DUST digest fields for this recovery-only adapter. Resolve recovery requests, observe a finalized receipt, then send `COMMIT` to acknowledge the private writes. Keep the recovery bytes and private host values out of logs.

Use `startDevelopmentDeployment(clientDescriptor, setup)` to fund and deploy the retained deployment. For an explicit-input proof, call `startDevelopmentCall(clientDescriptor, setup)` with its private journal setup. [Development instrumentation](../../sdk/android/tests/DevelopmentSmoke.kt)

## Run the Android smoke test

Use an arm64 Android emulator. Set `ANDROID_SDK_ROOT` to the SDK with platform 35 and Build Tools 35.0.0, and set `KOTLIN_HOME` to the Kotlin installation. Select your disposable emulator serial with `adb devices`.

```sh
.lake/build/bin/noctium compile tests/WitnessSource.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --emit control --output build/android-witness-plans
bash sdk/android/tests/package-smoke.sh build/noctium-android.aar \
  build/android-witness-plans/TypedWitness.scalarHost.control.json build/noctium-witness-smoke.apk
adb -s EMULATOR_SERIAL install build/noctium-witness-smoke.apk
adb -s EMULATOR_SERIAL shell am instrument -w -r org.noctium.sdk.tests/.WitnessSmoke
```

Pass a fourth argument to `package-smoke.sh` to include the authenticated proof case. Point it at a directory containing `bundle/` for the scalar typed-witness claim, the matching K7 parameters in `srs`, and its pinned descriptor in `target.json`. The APK copies the bundle into app-private storage and supplies `bundleDirectory`.

For the development transaction test, pass `--localnet` to `package-smoke.sh` and use the localnet AAR. Add `localnet/client.json`, `localnet/localnet.json` and `localnet/params/` to the public proof fixture. The parameter directory contains the pinned DUST files and the K13 SRS selected by the DUST circuit. The test replaces the journal and cache paths with app-private paths.

```sh
adb -s EMULATOR_SERIAL reverse tcp:19944 tcp:19944
adb -s EMULATOR_SERIAL shell am instrument -w -r org.noctium.sdk.tests/.DevelopmentSmoke
```

Use the test's loopback endpoint on port 19944 and run funded tests sharing the same development seed serially. Check for instrumentation code `-1` and the transaction and private recovery result.

## Replay the Compact-matched List fixture

Build the default ARM64 AAR and package the smoke APK on the same SDK as
the witness smoke test. If your SDK uses a different installed Build Tools
version, set `ANDROID_BUILD_TOOLS_VERSION` for the smoke APK build.

```sh
set -eu
mkdir -p build/experiments
scratch=$(mktemp -d "$PWD/build/experiments/android-list-pages.XXXXXX")
trap 'rm -rf -- "$scratch"' EXIT
bash sdk/android/package.sh "$scratch/noctium-android.aar"
bash sdk/android/tests/package-smoke.sh --collection-pages \
  "$scratch/noctium-android.aar" "$scratch/noctium-collection-pages.apk"
adb -s "$EMULATOR_SERIAL" install "$scratch/noctium-collection-pages.apk"
adb -s "$EMULATOR_SERIAL" shell am instrument -w -r \
  org.noctium.sdk.tests/.CollectionPagesSmoke
```

Expect instrumentation code `-1` and the marker
`NOCTIUM_ANDROID_COLLECTION_PAGES_PASS`. The test uses the retained plan
and empty and populated snapshots. It checks the empty List, `[11, 22]`
at offset zero, and `[33]` at the returned offset two. The last page
returns `null` for `nextOffset`. A request with an altered state digest
must fail with status `1` (`NOCTIUM_NATIVE_INVALID_ARGUMENT`).
[Fixture manifest and trusted digests](../../tests/fixtures/native-collection-pages/manifest.json) ·
[Compact and native fixture reproduction](native-client-abi.md#replay-the-scalar-collection-fixture)

## Reproduce the original one-time claim

Use the same development APK command with a fixture directory for `PrivateClaim.claim`. Include its authenticated `bundle/`, the K9 parameters in `srs` and the pinned proof options in `target.json`. Add the public development inputs from the claim fixture generator as `synthetic-claim.json`. This file selects the K9 case and becomes an APK test asset. Use synthetic inputs. [Fixture generation](native-contract.md#compile-the-actual-lean-source)

Capture the instrumentation output. Expect code `-1` and the marker `Noctium Android K9 private claim passed`. Decode the hex following `NOCTIUM_PUBLIC_STATE` into a binary state file. For the native replay check, use the bundle plan as `source-plan.json`, its relation as `zkir/claim.zkir`, `ledger.params`, the synthetic inputs as `runtime-config.json` and a `native-contract.json` containing the finalized contract address under `address`. [Native replay workflow](swift-witness-sdk.md#qualification)

```sh
noctium-runtime ARTIFACT_DIRECTORY --check-state STATE_FILE --expect-rejection
```

## Qualification

The default proof APK passed on the arm64 AOSP Android 35 emulator with Rust 1.100.0, NDK r30, Kotlin 1.9.24 and Temurin 21. It completed five typed callbacks, read a staged value, rejected a crossed reply, and generated and verified a K7 proof after producing result 14. It rejected an altered control plan and an incomplete witness. The default AAR measured 7,343,471 bytes. [Witness instrumentation](../../sdk/android/tests/WitnessSmoke.kt)

The development APK funded and finalized the typed-witness deployment at block 29716 and its call at block 29719. It rejected an altered signing request and detach during active work. A fresh client and seedless adapter reopened the on-disk journal and recovered the exact sealed transaction bytes. The 1,482 finalized contract-state bytes match both Swift runs by SHA-256. The private value committed after finality. The tested development AAR measured 19,772,800 bytes. [Typed-witness receipts](android-localnet-receipt.json) · [Transaction instrumentation](../../sdk/android/tests/DevelopmentSmoke.kt)

The original one-time claim finalized deployment at block 29781 and the claim at block 29784. The Android prover rejected a changed secret before submission. The pinned ZKIR tool sized the circuit at K9 and 297 rows. The 1,874 finalized state bytes match the Swift reference by SHA-256, and the native checker rejected reuse against those bytes. The tested development AAR measured 19,791,423 bytes. Physical Android hardware remains unverified. [Original claim receipts](android-private-claim-receipt.json)
