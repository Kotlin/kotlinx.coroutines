package kotlinx.coroutines

internal actual val DEBUG: Boolean = false

internal actual val Any.hexAddress: String
    get() = this.hashCode().toString()

internal actual val Any.classSimpleName: String get() = this::class.simpleName ?: "Unknown"

internal actual inline fun assert(value: () -> Boolean) {}

internal external interface Console {
    fun error(s: String)
}

internal external val console: Console