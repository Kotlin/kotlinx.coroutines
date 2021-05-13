/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import org.junit.*

/**
 * Tests that shared flows keep strong reference to their source flows.
 * See https://github.com/Kotlin/kotlinx.coroutines/issues/2557
 */
@OptIn(DelicateCoroutinesApi::class)
class SharingReferenceTest : TestBase() {
    private val token = object {}

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
        val flow = weakEmitter.shareIn(GlobalScope, SharingStarted.Eagerly, 0)
        FieldWalker.assertReachableCount(1, flow) { it === token }
    }

    @Test
    fun testStateInReference() {
        val flow = weakEmitter.stateIn(GlobalScope, SharingStarted.Eagerly, null)
        FieldWalker.assertReachableCount(1, flow) { it === token }
    }

    @Test
    fun testStateInSuspendingReference() = runTest {
        val flow = weakEmitter.stateIn(GlobalScope)
        FieldWalker.assertReachableCount(1, flow) { it === token }
    }
}