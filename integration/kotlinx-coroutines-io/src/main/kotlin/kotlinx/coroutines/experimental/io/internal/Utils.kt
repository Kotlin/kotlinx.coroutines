package kotlinx.coroutines.experimental.io.internal

import kotlinx.coroutines.experimental.io.ByteOrder
import java.nio.*
import java.util.concurrent.atomic.*
import kotlin.reflect.*

internal fun ByteBuffer.isEmpty() = !hasRemaining()

val ByteOrder.forNio: java.nio.ByteOrder
    get() = when (this) {
        ByteOrder.BIG_ENDIAN -> java.nio.ByteOrder.BIG_ENDIAN
        ByteOrder.LITTLE_ENDIAN -> java.nio.ByteOrder.LITTLE_ENDIAN
    }

internal inline fun <reified Owner : Any> longUpdater(p: KProperty1<Owner, Long>): AtomicLongFieldUpdater<Owner> {
    return AtomicLongFieldUpdater.newUpdater(Owner::class.java, p.name)
}

internal inline fun <reified Owner : Any> intUpdater(p: KProperty1<Owner, Int>): AtomicIntegerFieldUpdater<Owner> {
    return AtomicIntegerFieldUpdater.newUpdater(Owner::class.java, p.name)
}

internal inline fun <reified Owner : Any, reified T> updater(p: KProperty1<Owner, T>): AtomicReferenceFieldUpdater<Owner, T> {
    return AtomicReferenceFieldUpdater.newUpdater(Owner::class.java, T::class.java, p.name)
}
