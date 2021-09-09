/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.exceptions

import kotlinx.coroutines.*
import kotlinx.coroutines.selects.*
import org.junit.*
import org.junit.rules.*

class StackTraceRecoverySelectTest : TestBase() {

    @get:Rule
    val name = TestName()

    @Test
    fun testSelectJoin() = runTest {
        expect(1)
        val result = runCatching { doSelect() }
        expect(3)
        verifyStackTrace("select/${name.methodName}", result.exceptionOrNull()!!)
        finish(4)
    }

    private suspend fun doSelect(): Int {
        val job = CompletableDeferred(Unit)
        return select {
            job.onJoin {
                yield() // Hide the stackstrace
                expect(2)
                throw RecoverableTestException()
            }
        }
    }

    @Test
    fun testSelectCompletedAwait() = runTest {
        val deferred = CompletableDeferred<Unit>()
        deferred.completeExceptionally(RecoverableTestException())
        val result = runCatching { doSelectAwait(deferred) }
        verifyStackTrace("select/${name.methodName}", result.exceptionOrNull()!!)
    }

    private suspend fun doSelectAwait(deferred: Deferred<Unit>): Int {
        return select {
            deferred.onAwait {
                yield() // Hide the stackstrace
                42
            }
        }
    }
}