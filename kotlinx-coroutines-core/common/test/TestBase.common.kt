/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.coroutines.*
import kotlinx.coroutines.internal.*

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

public class TestException(message: String? = null) : Throwable(message), NonRecoverableThrowable
public class TestException1(message: String? = null) : Throwable(message), NonRecoverableThrowable
public class TestException2(message: String? = null) : Throwable(message), NonRecoverableThrowable
public class TestException3(message: String? = null) : Throwable(message), NonRecoverableThrowable
public class TestRuntimeException(message: String? = null) : RuntimeException(message), NonRecoverableThrowable
public class RecoverableTestException(message: String? = null) : RuntimeException(message)

public fun wrapperDispatcher(context: CoroutineContext): CoroutineContext {
    val dispatcher = context[ContinuationInterceptor] as CoroutineDispatcher
    return object : CoroutineDispatcher() {
        override fun dispatch(context: CoroutineContext, block: Runnable) {
            dispatcher.dispatch(context, block)
        }
    }
}