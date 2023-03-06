/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test.internal

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.test.*
import kotlin.coroutines.*

/**
 * The testable main dispatcher used by kotlinx-coroutines-test.
 * It is a [MainCoroutineDispatcher] that delegates all actions to a settable delegate.
 */
internal class TestMainDispatcher(delegate: CoroutineDispatcher):
    MainCoroutineDispatcher(),
    Delay
{
    private val mainDispatcher = delegate
    private var delegate = NonConcurrentlyModifiable(mainDispatcher, "Dispatchers.Main")

    private val delay
        get() = delegate.value as? Delay ?: defaultDelay

    override val immediate: MainCoroutineDispatcher
        get() = (delegate.value as? MainCoroutineDispatcher)?.immediate ?: this

    override fun dispatch(context: CoroutineContext, block: Runnable) = delegate.value.dispatch(context, block)

    override fun isDispatchNeeded(context: CoroutineContext): Boolean = delegate.value.isDispatchNeeded(context)

    override fun dispatchYield(context: CoroutineContext, block: Runnable) = delegate.value.dispatchYield(context, block)

    fun setDispatcher(dispatcher: CoroutineDispatcher) {
        delegate.value = dispatcher
    }

    fun resetDispatcher() {
        delegate.value = mainDispatcher
    }

    override fun scheduleResumeAfterDelay(timeMillis: Long, continuation: CancellableContinuation<Unit>) =
        delay.scheduleResumeAfterDelay(timeMillis, continuation)

    override fun invokeOnTimeout(timeMillis: Long, block: Runnable, context: CoroutineContext): DisposableHandle =
        delay.invokeOnTimeout(timeMillis, block, context)

    companion object {
        internal val currentTestDispatcher
            get() = (Dispatchers.Main as? TestMainDispatcher)?.delegate?.value as? TestDispatcher

        internal val currentTestScheduler
            get() = currentTestDispatcher?.scheduler
    }

    /**
     * A wrapper around a value that attempts to throw when writing happens concurrently with reading.
     *
     * The read operations never throw. Instead, the failures detected inside them will be remembered and thrown on the
     * next modification.
     */
    private class NonConcurrentlyModifiable<T>(initialValue: T, private val name: String) {
        private val reader: AtomicRef<Throwable?> = atomic(null) // last reader to attempt access
        private val readers = atomic(0) // number of concurrent readers
        private val writer: AtomicRef<Throwable?> = atomic(null) // writer currently performing value modification
        private val exceptionWhenReading: AtomicRef<Throwable?> = atomic(null) // exception from reading
        private val _value = atomic(initialValue) // the backing field for the value

        private fun concurrentWW(location: Throwable) = IllegalStateException("$name is modified concurrently", location)
        private fun concurrentRW(location: Throwable) = IllegalStateException("$name is used concurrently with setting it", location)

        var value: T
            get() {
                reader.value = Throwable("reader location")
                readers.incrementAndGet()
                writer.value?.let { exceptionWhenReading.value = concurrentRW(it) }
                val result = _value.value
                readers.decrementAndGet()
                return result
            }
            set(value) {
                exceptionWhenReading.getAndSet(null)?.let { throw it }
                if (readers.value != 0) reader.value?.let { throw concurrentRW(it) }
                val writerLocation = Throwable("other writer location")
                writer.getAndSet(writerLocation)?.let { throw concurrentWW(it) }
                _value.value = value
                writer.compareAndSet(writerLocation, null)
                if (readers.value != 0) reader.value?.let { throw concurrentRW(it) }
            }
    }
}

@Suppress("INVISIBLE_MEMBER")
private val defaultDelay
    inline get() = DefaultDelay

@Suppress("INVISIBLE_MEMBER")
internal expect fun Dispatchers.getTestMainDispatcher(): TestMainDispatcher
