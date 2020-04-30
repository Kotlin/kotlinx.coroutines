/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("unused")

package kotlinx.coroutines

import kotlinx.coroutines.flow.*
import kotlin.coroutines.*
import kotlin.test.*

expect val isStressTest: Boolean
expect val stressTestMultiplier: Int

expect open class TestBase constructor() {
    fun error(message: Any, cause: Throwable? = null): Nothing
    fun expect(index: Int)
    fun expectUnreached()
    fun finish(index: Int)
    fun ensureFinished() // Ensures that 'finish' was invoked
    fun reset() // Resets counter and finish flag. Workaround for parametrized tests absence in common

    fun runTest(
        expected: ((Throwable) -> Boolean)? = null,
        unhandled: List<(Throwable) -> Boolean> = emptyList(),
        block: suspend CoroutineScope.() -> Unit
    )
}

suspend inline fun hang(onCancellation: () -> Unit) {
    try {
        suspendCancellableCoroutine<Unit> { }
    } finally {
        onCancellation()
    }
}

inline fun <reified T : Throwable> assertFailsWith(block: () -> Unit) {
    try {
        block()
        error("Should not be reached")
    } catch (e: Throwable) {
        assertTrue(e is T)
    }
}

suspend inline fun <reified T : Throwable> assertFailsWith(flow: Flow<*>) {
    try {
        flow.collect()
        fail("Should be unreached")
    } catch (e: Throwable) {
        assertTrue(e is T, "Expected exception ${T::class}, but had $e instead")
    }
}

suspend fun Flow<Int>.sum() = fold(0) { acc, value -> acc + value }
suspend fun Flow<Long>.longSum() = fold(0L) { acc, value -> acc + value }


// data is added to avoid stacktrace recovery because CopyableThrowable is not accessible from common modules
class TestException(message: String? = null, private val data: Any? = null) : Throwable(message)
class TestException1(message: String? = null, private val data: Any? = null) : Throwable(message)
class TestException2(message: String? = null, private val data: Any? = null) : Throwable(message)
class TestException3(message: String? = null, private val data: Any? = null) : Throwable(message)
class TestCancellationException(message: String? = null, private val data: Any? = null) : CancellationException(message)
class TestRuntimeException(message: String? = null, private val data: Any? = null) : RuntimeException(message)
class RecoverableTestException(message: String? = null) : RuntimeException(message)
class RecoverableTestCancellationException(message: String? = null) : CancellationException(message)

fun wrapperDispatcher(context: CoroutineContext): CoroutineContext {
    val dispatcher = context[ContinuationInterceptor] as CoroutineDispatcher
    return object : CoroutineDispatcher() {
        override fun isDispatchNeeded(context: CoroutineContext): Boolean =
            dispatcher.isDispatchNeeded(context)
        override fun dispatch(context: CoroutineContext, block: Runnable) =
            dispatcher.dispatch(context, block)
    }
}

suspend fun wrapperDispatcher(): CoroutineContext = wrapperDispatcher(coroutineContext)

class BadClass {
    override fun equals(other: Any?): Boolean = error("equals")
    override fun hashCode(): Int = error("hashCode")
    override fun toString(): String = error("toString")
}
