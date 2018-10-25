/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

public expect open class TestBase constructor() {
    public val isStressTest: Boolean
    public val stressTestMultiplier: Int

    public fun error(message: Any, cause: Throwable? = null): Nothing
    public fun expect(index: Int)
    public fun expectUnreached()
    public fun finish(index: Int)
    public fun reset() // Resets counter and finish flag. Workaround for parametrized tests absence in common

    public fun runTest(
        expected: ((Throwable) -> Boolean)? = null,
        unhandled: List<(Throwable) -> Boolean> = emptyList(),
        block: suspend CoroutineScope.() -> Unit
    )
}

public class TestException(message: String? = null) : Throwable(message)
public class TestException1(message: String? = null) : Throwable(message)
public class TestException2(message: String? = null) : Throwable(message)
public class TestException3(message: String? = null) : Throwable(message)
public class TestRuntimeException(message: String? = null) : RuntimeException(message)
