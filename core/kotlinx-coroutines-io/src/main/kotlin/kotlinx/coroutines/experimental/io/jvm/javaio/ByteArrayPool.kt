package kotlinx.coroutines.experimental.io.jvm.javaio

import kotlinx.io.pool.*

internal val ByteArrayPool = object : DefaultPool<ByteArray>(128) {
    override fun produceInstance() = ByteArray(4096)
}