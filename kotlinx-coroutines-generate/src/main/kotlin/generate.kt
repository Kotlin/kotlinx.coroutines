package kotlinx.coroutines

import java.util.*

/**
 * Creates a Sequence object based on received coroutine [c].
 *
 * Each call of yield suspend function within the coroutine lambda generates
 * next element of resulting sequence. Calling yieldAll suspend function can be used to
 * yield sequence of values efficiently.
 */
fun <T> generate(coroutine c: GeneratorController<T>.() -> Continuation<Unit>): Sequence<T> =
        object : NestedIterable<T> {
            override fun nestedIterator(): NestedIterator<T> {
                val iterator = GeneratorController<T>()
                iterator.setNextStep(iterator.c())
                return iterator
            }
        }

class GeneratorController<T> internal constructor() : NestedIterator<T>() {
    private lateinit var nextStep: Continuation<Unit>

    override fun computeNextItemOrIterator() {
        nextStep.resume(Unit)
    }

    internal fun setNextStep(step: Continuation<Unit>) {
        nextStep = step
    }

    suspend fun yield(value: T, c: Continuation<Unit>) {
        setNext(value)
        setNextStep(c)
    }

    private fun yieldFromIterator(iterator: Iterator<T>, c: Continuation<Unit>) {
        setNextIterator(iterator)
        setNextStep(c)
    }

    suspend fun yieldAll(values: Sequence<T>, c: Continuation<Unit>) {
        yieldFromIterator(if (values is NestedIterable<T>)
                              values.nestedIterator() else
                              values.iterator(), c)
    }

    suspend fun yieldAll(values: Iterable<T>, c: Continuation<Unit>) {
        yieldFromIterator(values.iterator(), c)
    }

    suspend fun yieldAll(vararg values: T, c: Continuation<Unit>) {
        yieldFromIterator(values.iterator(), c)
    }

    operator fun handleResult(result: Unit, c: Continuation<Nothing>) {
        done()
    }
}

/**
 * Extends [AbstractIterator] adding it the ability to produce a next nested iterator instead of a next item.
 * If [hasNext] is true, then either a next item or a next nested iterator is produced.
 *
 * If [nextNestedIterator] != null, the consumer should use the items from [nextNestedIterator]
 * and then continue iterating over this iterator. Also if a next nested iterator is produced,
 * the value returned by [next] should not be used as it is invalid, but [next] should still be called.
 * Therefore [NestedIterator] cannot be used as a normal iterator.
 */
abstract class NestedIterator<T> internal constructor() : AbstractIterator<T>() {
    /**
     * Either `null` or the iterator that should be used before continuing iteration over this iterator.
     * If [hasNext] is true and nextNestedIterator is null, then there's no next iterator.
     */
    internal var nextNestedIterator: Iterator<T>? = null
        private set

    final override fun computeNext(): Unit {
        nextNestedIterator = null
        computeNextItemOrIterator()
    }

    /**
     * Computes the next item or a next nested iterator of this iterator.
     *
     * This callback method should call one of these three methods:
     *
     * * [setNext] with the next value of the iteration
     * * [setNextIterator] with the next nested iterator of the iteration
     * * [done] to indicate there are no more elements
     *
     * Failure to call either method will result in the iteration terminating with a failed state
     */
    internal abstract fun computeNextItemOrIterator()

    protected fun setNextIterator(iterator: Iterator<T>) {
        nextNestedIterator = iterator
        setNext(null as T) //state transfer to Ready
    }
}

/**
 * Manages [NestedIterator]s, arranging them in a stack and switching between them as they produce next
 * nested iterators or finish.
 * The concept is taken from
 * [this article](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/specsharp-iterators.pdf).
 */
private class RootIterator<T> constructor(iterator: Iterator<T>) : AbstractIterator<T>() {
    private val stack = Stack<Iterator<T>>().apply { push(iterator) }

    override fun computeNext() {
        while (true) {
            if (stack.isEmpty()) {
                done()
                return
            }
            val i = stack.peek()
            if (!i.hasNext()) {
                stack.pop()
            } else {
                if (i is NestedIterator<T> && i.nextNestedIterator != null) {
                    stack.push(i.nextNestedIterator)
                    i.next() //state transfer to NotReady
                } else {
                    setNext(i.next())
                    return
                }
            }
        }
    }
}

/**
 * Default implementation of [Sequence] for [NestedIterator] providers.
 */
private interface NestedIterable<T> : Sequence<T> {
    fun nestedIterator(): NestedIterator<T>
    override fun iterator(): Iterator<T> = RootIterator(nestedIterator())
}