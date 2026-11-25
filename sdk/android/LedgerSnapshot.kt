package org.noctium.sdk

/** Reads a bounded collection page from a pinned public ledger snapshot. */
object LedgerSnapshot {
    @JvmStatic
    fun collectionPage(request: ByteArray, plan: ByteArray, snapshot: ByteArray): ByteArray =
        Native.collectionPage(request, plan, snapshot)
}
