package kotlinx.coroutines.experimental.internal

internal actual fun <E> arraycopy(source: Array<E>, srcPos: Int, destination: Array<E?>, destinationStart: Int, length: Int) {
    var destinationIndex = destinationStart
    for (sourceIndex in srcPos until srcPos + length) {
        destination[destinationIndex++] = source[sourceIndex]
    }
}
