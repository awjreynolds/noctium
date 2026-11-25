package org.noctium.sdk.tests

import android.app.Activity
import android.app.Instrumentation
import android.os.Bundle
import org.json.JSONArray
import org.json.JSONObject
import org.noctium.sdk.LedgerSnapshot
import org.noctium.sdk.NoctiumFailure

class CollectionPagesSmoke : Instrumentation() {
    override fun onCreate(arguments: Bundle?) {
        super.onCreate(arguments)
        start()
    }

    override fun onStart() {
        try {
            runCollectionPages()
            finish(Activity.RESULT_OK, Bundle().apply {
                putString("stream", "$PASS_MARKER\n")
            })
        } catch (error: Throwable) {
            val status = (error as? NoctiumFailure)?.let { " status ${it.status}" }.orEmpty()
            finish(Activity.RESULT_CANCELED, Bundle().apply {
                putString(
                    "stream",
                    "$FAIL_MARKER: ${error.javaClass.simpleName} ${error.message.orEmpty()}" +
                        "$status ${error.stackTrace.firstOrNull()}\n",
                )
            })
        }
    }

    private fun runCollectionPages() {
        val manifest = JSONObject(readAsset("manifest.json").toString(Charsets.UTF_8))
        val planMetadata = manifest.getJSONObject("plan")
        check(planMetadata.getString("file") == "plan.impact.json")
        val planDigest = planMetadata.getString("sha256")
        val snapshots = manifest.getJSONObject("snapshots")
        val emptyMetadata = snapshots.getJSONObject("empty")
        val populatedMetadata = snapshots.getJSONObject("populated")
        check(emptyMetadata.getString("file") == "empty.state")
        check(populatedMetadata.getString("file") == "populated.state")

        val plan = readAsset(planMetadata.getString("file"))
        val empty = readAsset(emptyMetadata.getString("file"))
        val populated = readAsset(populatedMetadata.getString("file"))

        assertListPage(page(planDigest, emptyMetadata.getString("sha256"), plan, empty, 0), emptyList(), null)

        val first = page(planDigest, populatedMetadata.getString("sha256"), plan, populated, 0)
        assertListPage(first, listOf("11", "22"), 2)

        val continuationOffset = first.getInt("nextOffset")
        check(continuationOffset == 2) { "expected continuation offset 2, got $continuationOffset" }
        val continuation = page(
            planDigest, populatedMetadata.getString("sha256"), plan, populated, continuationOffset,
        )
        assertListPage(continuation, listOf("33"), null)

        val validStateDigest = populatedMetadata.getString("sha256")
        val tamperedStateDigest = if (validStateDigest[0] == '0') {
            "1${validStateDigest.substring(1)}"
        } else {
            "0${validStateDigest.substring(1)}"
        }
        expectInvalidArgument {
            page(planDigest, tamperedStateDigest, plan, populated, 0)
        }
    }

    private fun page(
        planDigest: String,
        stateDigest: String,
        plan: ByteArray,
        snapshot: ByteArray,
        offset: Int,
    ): JSONObject {
        val request = JSONObject()
            .put("abiVersion", 1)
            .put("planSha256", planDigest)
            .put("stateSha256", stateDigest)
            .put("name", "values")
            .put("keys", JSONArray())
            .put("offset", offset)
            .put("limit", 2)
            .toString()
            .toByteArray(Charsets.UTF_8)
        return JSONObject(LedgerSnapshot.collectionPage(request, plan, snapshot).toString(Charsets.UTF_8))
    }

    private fun assertListPage(actual: JSONObject, expected: List<String>, nextOffset: Int?) {
        check(actual.length() == 4) { "unexpected collection page fields: $actual" }
        check(actual.getInt("abiVersion") == 1)
        check(actual.getString("kind") == "list")
        val entries = actual.getJSONArray("entries")
        check(entries.length() == expected.size) { "unexpected list entries: $entries" }
        for (index in expected.indices) {
            check(entries.get(index) == expected[index]) { "unexpected list entry at $index: $entries" }
        }

        val actualNext = actual.get("nextOffset")
        if (nextOffset == null) {
            check(actualNext === JSONObject.NULL) { "expected no next offset, got $actualNext" }
        } else {
            check(actualNext is Number && actualNext.toInt() == nextOffset) {
                "expected next offset $nextOffset, got $actualNext"
            }
        }
    }

    private fun expectInvalidArgument(action: () -> Unit) {
        try {
            action()
        } catch (error: NoctiumFailure) {
            check(error.status == NOCTIUM_NATIVE_INVALID_ARGUMENT) {
                "expected invalid argument status $NOCTIUM_NATIVE_INVALID_ARGUMENT, got ${error.status}"
            }
            return
        }
        error("Expected a tampered snapshot digest to fail")
    }

    private fun readAsset(name: String): ByteArray =
        targetContext.assets.open("native-collection-pages/$name").use { it.readBytes() }

    private companion object {
        const val PASS_MARKER = "NOCTIUM_ANDROID_COLLECTION_PAGES_PASS"
        const val FAIL_MARKER = "NOCTIUM_ANDROID_COLLECTION_PAGES_FAIL"

        // Matches NOCTIUM_NATIVE_INVALID_ARGUMENT in runtime/include/noctium_native.h.
        const val NOCTIUM_NATIVE_INVALID_ARGUMENT = 1
    }
}
