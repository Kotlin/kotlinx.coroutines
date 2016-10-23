package kotlinx.coroutines

/**
 * Creates a Sequence object based on received coroutine [c].
 *
 * Each call of 'yield' suspend function within the coroutine lambda generates
 * next element of resulting sequence.
 */
fun <T> generate(
        coroutine c: GeneratorController<T>.() -> Continuation<Unit>
): Sequence<T> =
        object : Sequence<T> {
            override fun iterator(): Iterator<T> {
                val iterator = GeneratorController<T>()
                iterator.setNextStep(c(iterator))
                return iterator
            }
        }

class GeneratorController<T> internal constructor() : AbstractIterator<T>() {
    private lateinit var nextStep: Continuation<Unit>

    override fun computeNext() {
        nextStep.resume(Unit)
    }

    internal fun setNextStep(step: Continuation<Unit>) {
        nextStep = step
    }

    suspend fun yield(value: T, c: Continuation<Unit>) {
        setNext(value)
        setNextStep(c)
    }

    suspend fun yieldAll(values: Iterable<T>, c: Continuation<Unit>) =
            yieldAll(values.iterator(), c)

    suspend fun yieldAll(values: Sequence<T>, c: Continuation<Unit>) =
            yieldAll(values.iterator(), c)

    suspend fun yieldAll(vararg values: T, c: Continuation<Unit>) =
            yieldAll(values.iterator(), c)

    private fun yieldAll(iterator: Iterator<T>, c: Continuation<Unit>) {
        val iteratorContinuation = object : Continuation<Unit> {
            override fun resume(data: Unit) =
                    if (iterator.hasNext())
                        yield(iterator.next(), this)
                    else
                        c.resume(Unit)

            override fun resumeWithException(exception: Throwable) =
                    c.resumeWithException(exception)
        }
        iteratorContinuation.resume(Unit)
    }

    operator fun handleResult(result: Unit, c: Continuation<Nothing>) {
        done()
    }
}
