package kotlinx.coroutines

import kotlin.math.*
import kotlin.native.*

internal actual val DEBUG: Boolean = false

internal actual val Any.hexAddress: String get() = identityHashCode().toUInt().toString(16)

internal actual val Any.classSimpleName: String get() = this::class.simpleName ?: "Unknown"

internal actual inline fun assert(value: () -> Boolean) {}
