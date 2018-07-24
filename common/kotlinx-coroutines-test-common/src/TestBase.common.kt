/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental

public expect open class TestBase constructor() {

    public fun error(message: Any, cause: Throwable? = null): Nothing
    public fun expect(index: Int)
    public fun expectUnreached()
    public fun finish(index: Int)

    public fun runTest(
        expected: ((Throwable) -> Boolean)? = null,
        unhandled: List<(Throwable) -> Boolean> = emptyList(),
        block: suspend CoroutineScope.() -> Unit
    )
}
