/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import org.junit.*

/**
 * Tests that shared flows keep strong reference to their source flows.
 * See https://github.com/Kotlin/kotlinx.coroutines/issues/2557
 */
@OptIn(DelicateCoroutinesApi::class)
class SharingReferenceTest : TestBase() {
    private val token = object {}

    /*
     * Single-threaded executor that we are using to ensure that the flow being sharing actually
     * suspended (spilled its locals, attached to parent), so we can verify reachability.
     * Without that, it's possible to have a situation where target flow is still
     * being strongly referenced (by its dispatcher), but the test already tries to test reachability and fails.
     */
    @get:Rule
    val executor = ExecutorRule(1)

    private val weakEmitter = flow {
        emit(null)
        // suspend forever without keeping a strong reference to continuation -- this is a model of
        // a callback API that does not keep a strong reference it is listeners, but works
        suspendCancellableCoroutine<Unit> {  }
        // using the token here to make it easily traceable
        emit(token)
    }

    @Test
    fun testShareInReference() {
        val flow = weakEmitter.shareIn(ContextScope(executor), SharingStarted.Eagerly, 0)
        linearize()
        FieldWalker.assertReachableCount(1, flow) { it === token }
    }

    @Test
    fun testStateInReference() {
        val flow = weakEmitter.stateIn(ContextScope(executor), SharingStarted.Eagerly, null)
        linearize()
        FieldWalker.assertReachableCount(1, flow) { it === token }
    }

    @Test
    fun testStateInSuspendingReference() = runTest {
        val flow = weakEmitter.stateIn(ContextScope(executor))
        linearize()
        FieldWalker.assertReachableCount(1, flow) { it === token }
    }

    private fun linearize() {
        runBlocking(executor) {  }
    }
}
