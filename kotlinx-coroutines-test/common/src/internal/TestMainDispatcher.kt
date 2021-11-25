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
internal class TestMainDispatcher(delegate: CoroutineDispatcher?, mainInitException: Throwable? = null):
    MainCoroutineDispatcher(),
    Delay {
    private val mainDispatcher = delegate ?: UnsetMainDispatcher(mainInitException)

    private var delegate = NonConcurrentlyModifiable(mainDispatcher, "Dispatchers.Main")

    private val delay
        get() = delegate.value as? Delay ?: nonMockedDelay

    override val immediate: MainCoroutineDispatcher
        get() = (delegate.value as? MainCoroutineDispatcher)?.immediate ?: this

    override fun dispatch(context: CoroutineContext, block: Runnable) = delegate.value.dispatch(context, block)

    override fun isDispatchNeeded(context: CoroutineContext): Boolean = delegate.value.isDispatchNeeded(context)

    override fun dispatchYield(context: CoroutineContext, block: Runnable) =
        delegate.value.dispatchYield(context, block)

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

    override fun toString(): String = "TestMainDispatcher[delegate=${delegate.value}]"

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
        private val readers = atomic(0) // number of concurrent readers
        private val isWriting = atomic(false) // a modification is happening currently
        private val exceptionWhenReading: AtomicRef<Throwable?> = atomic(null) // exception from reading
        private val _value = atomic(initialValue) // the backing field for the value

        private fun concurrentWW() = IllegalStateException("$name is modified concurrently")
        private fun concurrentRW() = IllegalStateException("$name is used concurrently with setting it")

        var value: T
            get() {
                readers.incrementAndGet()
                if (isWriting.value) exceptionWhenReading.value = concurrentRW()
                val result = _value.value
                readers.decrementAndGet()
                return result
            }
            set(value) {
                exceptionWhenReading.getAndSet(null)?.let { throw it }
                if (readers.value != 0) throw concurrentRW()
                if (!isWriting.compareAndSet(expect = false, update = true)) throw concurrentWW()
                _value.value = value
                isWriting.value = false
                if (readers.value != 0) throw concurrentRW()
            }
    }

    private class UnsetMainDispatcher(private val mainInitException: Throwable?) : MainCoroutineDispatcher() {
        override val immediate: MainCoroutineDispatcher get() = this
        override fun isDispatchNeeded(context: CoroutineContext): Boolean = missing()
        override fun limitedParallelism(parallelism: Int): CoroutineDispatcher = missing()
        override fun dispatch(context: CoroutineContext, block: Runnable) = missing()

        private fun missing(): Nothing {
            val message = if (mainInitException == null)
                "Dispatchers.Main is not available was not provided for tests via Dispatchers.setMain."
            else
                "Dispatchers.Main failed to initialize and was not replaced via Dispatchers.setMain."
            throw IllegalStateException(message, mainInitException)
        }

        override fun toString(): String = "missing"
    }
}

internal expect val nonMockedDelay: Delay

internal expect fun Dispatchers.getTestMainDispatcher(): TestMainDispatcher