package kotlinx.coroutines.experimental.internal

/**
 * Cross-platform array copy. Overlaps of source and destination are not supported
 */
expect fun <E> arraycopy(source: Array<E>, srcPos: Int, destination: Array<E?>, destinationStart: Int, length: Int)