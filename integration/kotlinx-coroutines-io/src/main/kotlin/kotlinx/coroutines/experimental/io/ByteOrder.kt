package kotlinx.coroutines.experimental.io

enum class ByteOrder {
    BIG_ENDIAN,
    LITTLE_ENDIAN;

    companion object {
        val native: ByteOrder = when (java.nio.ByteOrder.nativeOrder()) {
            java.nio.ByteOrder.BIG_ENDIAN -> BIG_ENDIAN
            java.nio.ByteOrder.LITTLE_ENDIAN -> LITTLE_ENDIAN
            else -> throw UnsupportedOperationException()
        }
    }
}