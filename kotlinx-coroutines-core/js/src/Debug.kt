package kotlinx.coroutines

private var counter = 0

internal actual val DEBUG: Boolean = false

internal actual val Any.hexAddress: String
    get() {
        var result = this.asDynamic().__debug_counter
        if (jsTypeOf(result) !== "number") {
            result = ++counter
            this.asDynamic().__debug_counter = result

        }
        return (result as Int).toString()
    }

internal actual val Any.classSimpleName: String get() = this::class.simpleName ?: "Unknown"

internal actual inline fun assert(value: () -> Boolean) {}
