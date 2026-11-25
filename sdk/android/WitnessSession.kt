package org.noctium.sdk

/** A status returned by the native runtime. */
class NoctiumFailure(val status: Int) : IllegalStateException("Noctium status $status")

/** Runs a compiler-emitted host-control plan. Keep all invocation data on your trusted host. */
class WitnessSession private constructor(private var handle: Long) : AutoCloseable {
    companion object {
        /** Takes the Control ABI's UTF-8 JSON envelope with plan, inputs and hostContext. */
        fun open(begin: ByteArray): WitnessSession = WitnessSession(Native.open(begin))

        internal fun openBound(target: Long, plan: ByteArray, begin: ByteArray): WitnessSession =
            WitnessSession(Native.targetWitness(target, plan, begin))
    }

    @Synchronized
    fun advance(): ByteArray = Native.advance(activeHandle())

    /** Pass a canonical correlated reply. Set typed to false for protocol v1. */
    @Synchronized
    fun resume(response: ByteArray, typed: Boolean = true): ByteArray =
        Native.resume(activeHandle(), response, typed)

    /** Returns host-private callback arguments and the staged-write overlay. */
    @Synchronized
    fun privateRequest(): ByteArray = Native.privateRequest(activeHandle())

    @Synchronized
    fun cancel(): ByteArray = Native.cancel(activeHandle())

    @Synchronized
    override fun close() {
        if (handle != 0L) {
            Native.close(handle)
            handle = 0L
        }
    }

    @Synchronized
    internal fun consume(action: (Long) -> Long): Long {
        val result = action(activeHandle())
        handle = 0L
        return result
    }

    private fun activeHandle(): Long {
        check(handle != 0L) { "Noctium witness session is closed" }
        return handle
    }
}

internal object Native {
    init { System.loadLibrary("noctium_jni") }

    external fun open(begin: ByteArray): Long
    external fun advance(handle: Long): ByteArray
    external fun resume(handle: Long, response: ByteArray, typed: Boolean): ByteArray
    external fun privateRequest(handle: Long): ByteArray
    external fun cancel(handle: Long): ByteArray
    external fun close(handle: Long)
    external fun targetOpen(descriptor: ByteArray, state: ByteArray, srs: ByteArray, entropy: ByteArray): Long
    external fun targetWitness(target: Long, plan: ByteArray, begin: ByteArray): Long
    external fun targetClose(target: Long)
    external fun proofPrepare(target: Long, witness: Long, descriptor: ByteArray, srs: ByteArray, entropy: ByteArray): Long
    external fun proofOpen(descriptor: ByteArray, configuration: ByteArray, srs: ByteArray, entropy: ByteArray): Long
    external fun proofAdvance(proof: Long): ByteArray
    external fun proofGenerate(proof: Long, entropy: ByteArray): ByteArray
    external fun proofAttach(proof: Long, metadata: ByteArray, response: ByteArray): ByteArray
    external fun proofCancel(proof: Long)
    external fun proofClose(proof: Long)
    external fun collectionPage(request: ByteArray, plan: ByteArray, snapshot: ByteArray): ByteArray
}
