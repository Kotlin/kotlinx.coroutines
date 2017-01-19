package kotlinx.coroutines.experimental

public class Try<out T> private constructor(private val _value: Any?) {
    private class Fail(val exception: Throwable) {
        override fun toString(): String = "Failure[$exception]"
    }

    public companion object {
        public operator fun <T> invoke(block: () -> T): Try<T> =
                try { Success(block()) } catch(e: Throwable) { Failure<T>(e) }
        public fun <T> Success(value: T) = Try<T>(value)
        public fun <T> Failure(exception: Throwable) = Try<T>(Fail(exception))
    }

    @Suppress("UNCHECKED_CAST")
    public val value: T get() = if (_value is Fail) throw _value.exception else _value as T

    public val exception: Throwable? get() = (_value as? Fail)?.exception

    override fun toString(): String = _value.toString()
}
