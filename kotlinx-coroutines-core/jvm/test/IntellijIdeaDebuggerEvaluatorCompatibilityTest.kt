/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import org.junit.Test
import kotlin.coroutines.*
import kotlin.test.*

class IntellijIdeaDebuggerEvaluatorCompatibilityTest {

    /*
     * This test verifies that our CoroutineScope is accessible to IDEA debugger.
     *
     * Consider the following scenario:
     * ```
     * runBlocking<Unit> { // this: CoroutineScope
     *     println("runBlocking")
     * }
     * ```
     * user puts breakpoint to `println` line, opens "Evaluate" window
     * and executes `launch { println("launch") }`. They (obviously) expect it to work, but
     * it won't: `{}` in `runBlocking` is `SuspendLambda` and `this` is an unused implicit receiver
     * that is removed by the compiler (because it's unused).
     *
     * But we still want to provide consistent user experience for functions with `CoroutineScope` receiver,
     * for that IDEA debugger tries to retrieve the scope via `kotlin.coroutines.coroutineContext[Job] as? CoroutineScope`
     * and with this test we're fixing this behaviour.
     *
     * Note that this behaviour is not carved in stone: IDEA fallbacks to `kotlin.coroutines.coroutineContext` for the context if necessary.
     */

    @Test
    fun testScopeIsAccessible() = runBlocking<Unit> {
        verify()

        withContext(Job()) {
            verify()
        }

        coroutineScope {
            verify()
        }

        supervisorScope {
            verify()
        }

    }

    private suspend fun verify() {
        val ctx = coroutineContext
        assertTrue { ctx.job is CoroutineScope }
    }
}
