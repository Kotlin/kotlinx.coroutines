package kotlinx.coroutines.internal

@Suppress("NOTHING_TO_INLINE")
internal actual inline fun isZeroCount(countOrElement: Any?): Boolean = countOrElement is Int && countOrElement == 0
