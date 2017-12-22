package kotlinx.coroutines.experimental.io

interface WriterSession {
    fun request(min: Int): ByteBuffer?
    fun written(n: Int)
}

interface WriterSuspendSession : WriterSession {
    suspend fun tryAwait(n: Int)
}
