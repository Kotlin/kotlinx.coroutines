package kotlinx.coroutines.experimental.io

import kotlinx.coroutines.experimental.io.internal.*
import java.io.*

/**
 * Reads from the channel to the specified [dst] byte buffer until one of the following:
 * - channel's end
 * - [dst] capacity exceeded
 * - [delimiter] bytes encountered
 *
 * If [delimiter] bytes encountered then these bytes remain unconsumed
 *
 * @return non-negative number of copied bytes, possibly 0
 */
suspend fun ByteReadChannel.readUntilDelimiter(delimiter: ByteBuffer, dst: ByteBuffer): Int {
    require(delimiter.hasRemaining())
    require(delimiter !== dst)

    var copied = 0
    var endFound = false

    lookAhead {
        do {
            val rc = tryCopyUntilDelimiter(delimiter, dst)
            if (rc == 0) break
            val size = if (rc < 0) {
                endFound = true
                -rc
            } else rc
            copied += size
        } while (dst.hasRemaining() && !endFound)
    }

    if (!dst.hasRemaining() || endFound) return copied

    return readUntilDelimiterSuspend(delimiter, dst, copied)
}

suspend fun ByteReadChannel.skipDelimiter(delimiter: ByteBuffer) {
    require(delimiter.hasRemaining())

    var found = false

    lookAhead {
        found = tryEnsureDelimiter(delimiter) == delimiter.remaining()
    }

    if (!found) {
        skipDelimiterSuspend(delimiter)
    }
}

private suspend fun ByteReadChannel.skipDelimiterSuspend(delimiter: ByteBuffer) {
    lookAheadSuspend {
        awaitAtLeast(delimiter.remaining())
        if (tryEnsureDelimiter(delimiter) != delimiter.remaining()) throw IOException("Broken delimiter occurred")
    }
}

private suspend fun ByteReadChannel.readUntilDelimiterSuspend(delimiter: ByteBuffer, dst: ByteBuffer, copied0: Int): Int {
    require(delimiter !== dst)
    require(copied0 >= 0)

    return lookAheadSuspend {
        var endFound = false
        var copied = copied0

        do {
            awaitAtLeast(1)
            val rc = tryCopyUntilDelimiter(delimiter, dst)
            if (rc == 0) {
                if (request(0, delimiter.remaining())?.startsWith(delimiter, 0) == true) {
                    break
                }
                if (!isClosedForRead) {
                    awaitAtLeast(delimiter.remaining())
                    continue
                }
            }

            val size = if (rc <= 0) {
                endFound = true
                -rc
            } else rc
            copied += size
        } while (dst.hasRemaining() && !endFound)

        copied
    }
}

/**
 * @return a positive number of bytes copied if no [delimiter] found yet or a negated number of bytes copied if
 * the delimited has been found, or 0 if no buffer available (not yet ready or EOF)
 */
private fun LookAheadSession.tryCopyUntilDelimiter(delimiter: ByteBuffer, dst: ByteBuffer): Int {
    var endFound = false
    val buffer = request(0, 1) ?: return 0
    val index = buffer.indexOfPartial(delimiter)
    val size = if (index != -1) {
        val found = minOf(buffer.remaining() - index, delimiter.remaining())
        val notKnown = delimiter.remaining() - found

        val next = if (notKnown > 0) request(index + found, notKnown) else null
        if (next != null) {
            if (next.startsWith(delimiter, found)) {
                endFound = true
                dst.putLimited(buffer, buffer.position() + index)
            } else {
                dst.putLimited(buffer, buffer.position() + index + 1)
            }
        } else {
            endFound = notKnown == 0
            dst.putLimited(buffer, buffer.position() + index)
        }
    } else {
        dst.putAtMost(buffer)
    }
    consumed(size)

    return if (endFound) -size else size
}

private fun LookAheadSession.tryEnsureDelimiter(delimiter: ByteBuffer): Int {
    val buffer = request(0, 1) ?: return 0
    val index = buffer.indexOfPartial(delimiter)
    if (index != 0) throw IOException("Failed to skip delimiter: actual bytes differ from delimiter bytes")

    val found = minOf(buffer.remaining() - index, delimiter.remaining())
    val notKnown = delimiter.remaining() - found

    val next = (if (notKnown > 0) request(index + found, notKnown) else null) ?: return found
    if (!next.startsWith(delimiter, found)) throw IOException("Failed to skip delimiter: actual bytes differ from delimiter bytes")

    consumed(delimiter.remaining())
    return delimiter.remaining()
}