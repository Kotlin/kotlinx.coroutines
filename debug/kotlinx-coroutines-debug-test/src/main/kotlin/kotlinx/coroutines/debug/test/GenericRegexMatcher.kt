package kotlinx.coroutines.debug.test

interface Matchable {
    fun match(other: Matchable): Boolean
}

sealed class Token<out T : Matchable> {
    abstract val symbol: T
}

data class Single<out T : Matchable>(override val symbol: T) : Token<T>()
data class ZeroOrMore<out T : Matchable>(override val symbol: T) : Token<T>()
data class OneOrMore<out T : Matchable>(override val symbol: T) : Token<T>()

fun <T : Matchable> matches(pattern: List<Token<T>>, data: List<T>): Boolean {
    if (pattern.isEmpty()) return data.isEmpty()
    if (pattern.isNotEmpty() && data.isEmpty()) return false
    val head = pattern.first()
    when (head) {
        is Single -> {
            return if (head.symbol.match(data.first())) matches(pattern.drop(1), data.drop(1))
            else false
        }
        is ZeroOrMore -> {
            return if (head.symbol.match(data.first()))
                matches(pattern, data.drop(1)) || matches(pattern.drop(1), data.drop(1))
            else matches(pattern.drop(1), data)
        }
        is OneOrMore -> {
            return if (head.symbol.match(data.first()))
                matches(pattern, data.drop(1)) || matches(pattern.drop(1), data.drop(1))
            else false
        }
    }
}
