package kotlinx.coroutines.experimental.io

interface LookAheadSession {
    /**
     * Marks [n] bytes as consumed so the corresponding range becomes available for writing
     */
    fun consumed(n: Int)

    /**
     * Request byte buffer range skipping [skip] bytes and [atLeast] bytes length
     * @return byte buffer for the requested range or null if it is impossible to provide such a buffer
     *
     * There are the following reasons for this function to return `null`:
     * - not enough bytes available yet (should be at least `skip + atLeast` bytes available)
     * - due to buffer fragmentation is is impossible to represent the requested range as a single byte buffer
     * - end of stream encountered and all bytes were consumed
     * - channel has been closed with an exception so buffer has been recycled
     */
    fun request(skip: Int, atLeast: Int): ByteBuffer?
}

interface LookAheadSuspendSession : LookAheadSession {
    /**
     * Suspend until [n] bytes become available or end of stream encountered (possibly due to exceptional close)
     */
    suspend fun awaitAtLeast(n: Int): Boolean
}

inline fun LookAheadSession.consumeEachRemaining(visitor: (ByteBuffer) -> Boolean) {
    do {
        val cont = request(0, 1)?.let {
            val s = it.remaining()
            val rc = visitor(it)
            consumed(s)
            rc
        } ?: false

        if (!cont) break
    } while (true)
}

