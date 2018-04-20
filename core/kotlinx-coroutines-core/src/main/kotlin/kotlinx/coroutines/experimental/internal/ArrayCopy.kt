package kotlinx.coroutines.experimental.internal

actual fun <E> arraycopy(source: Array<E>, srcPos: Int, destination: Array<E?>, destinationStart: Int, length: Int){
    System.arraycopy(source, srcPos, destination, destinationStart, length)
}