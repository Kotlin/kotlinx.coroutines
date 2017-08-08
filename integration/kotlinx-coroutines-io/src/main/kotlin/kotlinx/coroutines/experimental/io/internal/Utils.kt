package kotlinx.coroutines.experimental.io.internal

import kotlinx.coroutines.experimental.io.ByteOrder
import java.nio.ByteBuffer
import java.util.concurrent.atomic.AtomicIntegerFieldUpdater
import java.util.concurrent.atomic.AtomicLongFieldUpdater
import java.util.concurrent.atomic.AtomicReferenceFieldUpdater
import kotlin.reflect.KProperty1

internal fun ByteBuffer.isEmpty() = !hasRemaining()

internal val ByteOrder.forNio: java.nio.ByteOrder
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

internal fun getIOIntProperty(name: String, default: Int): Int =
    try { System.getProperty("kotlinx.coroutines.io.$name") }
    catch (e: SecurityException) { null }
        ?.toIntOrNull() ?: default
