package kotlinx.coroutines.debug.test

import kotlinx.coroutines.debug.manager.CoroutineInfoItem
import java.util.regex.Pattern

private val Any?.p: String
    get() = if (this == null) ".*" else "$this".q

private val String.q: String
    get() = Pattern.quote(this)

sealed class RegexHolder(val regex: String)

sealed class StackItem(regex: String) : RegexHolder(regex)
data class CoroutineMarker(val name: String, val current: Boolean = false)
    : StackItem("${CoroutineInfoItem(name, current)}".q)

data class StackElement(val method: String?, val file: String? = null, val line: Int? = null)
    : StackItem(" {4}at ${method.p}\\(${file.p}${if (line == null) ".*" else ":${line.p}"}\\)")

sealed class Status(status: String, additionalInfo: String = "") : RegexHolder(" {2}Status: $status $additionalInfo")
data class Suspended(val atMethod: String? = null) : Status("Suspended", "at ${atMethod.p}")
data class Created(val onThread: String? = null) : Status("Created", "on ${onThread.p}")
data class Running(val onThread: String? = null) : Status("Running", "on ${onThread.p}")

data class RegexStringMatcher(val string: String) : Matchable {
    constructor(stackElement: RegexHolder) : this(stackElement.regex)

    override fun match(other: Matchable) =
            other is RegexStringMatcher && string.toRegex().matchEntire(other.string) != null
}

abstract class WithMatchablePattern<T : Matchable> {
    abstract val pattern: MutableList<Token<T>>
    fun match(data: List<T>) = matches(pattern, data)
}

abstract class FullStringMatcher : WithMatchablePattern<RegexStringMatcher>() {
    fun matchEntireString(string: String) = match(string.split('\n').map { RegexStringMatcher(it) })
}

class Coroutine(val name: String, val status: Status) : FullStringMatcher() {
    override val pattern: MutableList<Token<RegexStringMatcher>>
            = mutableListOf(Single(RegexStringMatcher("\\\"${name.q}\\\".*")), Single(RegexStringMatcher(status)))

    val any = StackElement(null)
    fun Int.methods(element: StackElement) =
            repeat(this) { pattern += Single(RegexStringMatcher(element)) }

    fun Int.methods(method: String?, file: String? = null, line: Int? = null) =
            methods(StackElement(method, file, line))

    fun marker(name: String, current: Boolean = false) {
        pattern += Single(RegexStringMatcher(CoroutineMarker(name, current)))
    }

    fun method(element: StackElement) {
        pattern += Single(RegexStringMatcher(element))
    }

    fun method(method: String?, file: String? = null, line: Int? = null) =
            method(StackElement(method, file, line))


    fun zeroOrMore(element: StackElement) {
        pattern += ZeroOrMore(RegexStringMatcher(element))
    }

    fun zeroOrMore(method: String?, file: String? = null, line: Int? = null) =
            zeroOrMore(StackElement(method, file, line))

    fun oneOrMore(element: StackElement) {
        pattern += OneOrMore(RegexStringMatcher(element))
    }

    fun oneOrMore(method: String?, file: String? = null, line: Int? = null) =
            oneOrMore(StackElement(method, file, line))
}

fun coroutine(name: String, status: Status, appendStack: Coroutine.() -> Unit = {}): Coroutine {
    val coroutine = Coroutine(name, status)
    coroutine.appendStack()
    return coroutine
}