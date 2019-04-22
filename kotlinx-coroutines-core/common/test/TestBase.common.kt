/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.flow.*
import kotlin.coroutines.*
import kotlinx.coroutines.internal.*
import kotlin.test.*

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

public suspend inline fun hang(onCancellation: () -> Unit) {
    try {
        suspendCancellableCoroutine<Unit> { }
    } finally {
        onCancellation()
    }
}

public inline fun <reified T : Throwable> assertFailsWith(block: () -> Unit) {
    try {
        block()
        error("Should not be reached")
    } catch (e: Throwable) {
        assertTrue(e is T)
    }
}

public suspend inline fun <reified T : Throwable> assertFailsWith(flow: Flow<*>) {
    var e: Throwable? = null
    var completed = false
    flow.launchIn(CoroutineScope(Dispatchers.Unconfined)) {
        onEach {}
        catch<Throwable> {
            e = it
        }
        finally {
            completed = true
            assertTrue(it is T)
        }
    }.join()
    assertTrue(e is T)
    assertTrue(completed)
}

public suspend fun Flow<Int>.sum() = fold(0) { acc, value -> acc + value }
public suspend fun Flow<Long>.longSum() = fold(0L) { acc, value -> acc + value }

public class TestException(message: String? = null) : Throwable(message), NonRecoverableThrowable
public class TestException1(message: String? = null) : Throwable(message), NonRecoverableThrowable
public class TestException2(message: String? = null) : Throwable(message), NonRecoverableThrowable
public class TestException3(message: String? = null) : Throwable(message), NonRecoverableThrowable
public class TestCancellationException(message: String? = null) : CancellationException(message), NonRecoverableThrowable
public class TestRuntimeException(message: String? = null) : RuntimeException(message), NonRecoverableThrowable
public class RecoverableTestException(message: String? = null) : RuntimeException(message)
public class RecoverableTestCancellationException(message: String? = null) : CancellationException(message)

public fun wrapperDispatcher(context: CoroutineContext): CoroutineContext {
    val dispatcher = context[ContinuationInterceptor] as CoroutineDispatcher
    return object : CoroutineDispatcher() {
        override fun dispatch(context: CoroutineContext, block: Runnable) {
            dispatcher.dispatch(context, block)
        }
    }
}

