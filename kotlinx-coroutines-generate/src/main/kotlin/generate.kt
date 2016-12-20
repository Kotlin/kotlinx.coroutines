package kotlinx.coroutines

import kotlin.coroutines.Continuation
import kotlin.coroutines.CoroutineIntrinsics
import kotlin.coroutines.RestrictsSuspension
import kotlin.coroutines.createCoroutine

/**
 * Scope of [generate] block.
 */
@RestrictsSuspension
public abstract class Generator<in T> internal constructor() {
    /**
     * Yields a value in [generate] block.
     */
    public abstract suspend fun yield(value: T)

    /**
     * Yields potentially infinite sequence of iterator values in [generate] block.
     */
    public abstract suspend fun yieldAll(iterator: Iterator<T>)

    /**
     * Yields a collections of values in [generate] block.
     */
    public suspend fun yieldAll(elements: Iterable<T>) = yieldAll(elements.iterator())

    /**
     * Yields potentially infinite sequence of values in [generate] block.
     */
    public suspend fun yieldAll(sequence: Sequence<T>) = yieldAll(sequence.iterator())
}

/**
 * Generates lazy sequence.
 */
public fun <T> generate(block: suspend Generator<T>.() -> Unit): Sequence<T> = object : Sequence<T> {
    override fun iterator(): Iterator<T> {
        val iterator = GeneratorIterator<T>()
        iterator.nextStep = block.createCoroutine(receiver = iterator, completion = iterator)
        return iterator
    }
}

private class GeneratorIterator<T>: Generator<T>(), Iterator<T>, Continuation<Unit> {
    var computedNext = false
    var nextStep: Continuation<Unit>? = null
    var nextValue: T? = null

    override fun hasNext(): Boolean {
        if (!computedNext) {
            val step = nextStep!!
            computedNext = true
            nextStep = null
            step.resume(Unit) // leaves it in "done" state if crashes
        }
        return nextStep != null
    }

    override fun next(): T {
        if (!hasNext()) throw NoSuchElementException()
        computedNext = false
        return nextValue as T
    }

    // Completion continuation implementation
    override fun resume(value: Unit) {
        // nothing to do here -- leave null in nextStep
    }

    override fun resumeWithException(exception: Throwable) {
        throw exception // just rethrow
    }

    // Generator implementation
    override suspend fun yield(value: T) {
        nextValue = value
        return CoroutineIntrinsics.suspendCoroutineOrReturn { c ->
            nextStep = c
            CoroutineIntrinsics.SUSPENDED
        }
    }

    override suspend fun yieldAll(iterator: Iterator<T>) {
        if (!iterator.hasNext()) return
        nextValue = iterator.next()
        return CoroutineIntrinsics.suspendCoroutineOrReturn { c ->
            nextStep = IteratorContinuation(c, iterator)
            CoroutineIntrinsics.SUSPENDED
        }
    }

    inner class IteratorContinuation(val completion: Continuation<Unit>, val iterator: Iterator<T>) : Continuation<Unit> {
        override fun resume(value: Unit) {
            if (!iterator.hasNext()) {
                completion.resume(Unit)
                return
            }
            nextValue = iterator.next()
            nextStep = this
        }

        override fun resumeWithException(exception: Throwable) {
            throw exception // just rethrow
        }
    }
}
