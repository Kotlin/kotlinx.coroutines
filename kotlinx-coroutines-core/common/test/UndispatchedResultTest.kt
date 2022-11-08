/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.coroutines.*
import kotlin.test.*

class UndispatchedResultTest : TestBase() {

    @Test
    fun testWithContext() = runTest {
        invokeTest { block -> withContext(wrapperDispatcher(coroutineContext), block) }
    }

    @Test
    fun testWithContextFastPath() = runTest {
        invokeTest { block -> withContext(coroutineContext, block) }
    }

    @Test
    fun testWithTimeout() = runTest {
        invokeTest { block -> withTimeout(Long.MAX_VALUE, block) }
    }

    @Test
    fun testAsync() = runTest {
        invokeTest { block -> async(NonCancellable, block = block).await() }
    }

    @Test
    fun testCoroutineScope() = runTest {
        invokeTest { block -> coroutineScope(block) }
    }

    private suspend fun invokeTest(scopeProvider: suspend (suspend CoroutineScope.() -> Unit) -> Unit) {
        invokeTest(EmptyCoroutineContext, scopeProvider)
        invokeTest(Unconfined, scopeProvider)
    }

    private suspend fun invokeTest(
        context: CoroutineContext,
        scopeProvider: suspend (suspend CoroutineScope.() -> Unit) -> Unit
    ) {
        try {
            scopeProvider { block(context) }
        } catch (e: TestException) {
            finish(5)
            reset()
        }
    }

    private suspend fun CoroutineScope.block(context: CoroutineContext) {
        try {
            expect(1)
            // Will cancel its parent
            async<Unit>(context) {
                expect(2)
                throw TestException()
            }.await()
        } catch (e: TestException) {
            expect(3)
        }
        expect(4)
    }
}
