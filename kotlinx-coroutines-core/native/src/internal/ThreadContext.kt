package kotlinx.coroutines.internal

internal actual fun isZeroCount(countOrElement: Any?): Boolean = countOrElement is Int && countOrElement == 0
