/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.channels.*
import kotlinx.coroutines.flow.internal.*
import kotlin.test.*

class CancelledParentAttachTest : TestBase() {

    @Test
    fun testAsync() = CoroutineStart.values().forEach(::testAsyncCancelledParent)

    private fun testAsyncCancelledParent(start: CoroutineStart) =
        runTest({ it is CancellationException }) {
            cancel()
            expect(1)
            val d = async<Int>(start = start) { 42 }
            expect(2)
            d.invokeOnCompletion {
                finish(3)
                reset()
            }
        }

    @Test
    fun testLaunch() = CoroutineStart.values().forEach(::testLaunchCancelledParent)

    private fun testLaunchCancelledParent(start: CoroutineStart) =
        runTest({ it is CancellationException }) {
            cancel()
            expect(1)
            val d = launch(start = start) { }
            expect(2)
            d.invokeOnCompletion {
                finish(3)
                reset()
            }
        }

    @Test
    fun testProduce() =
        runTest({ it is CancellationException }) {
            cancel()
            expect(1)
            val d = produce<Int> { }
            expect(2)
            (d as Job).invokeOnCompletion {
                finish(3)
                reset()
            }
        }

    @Test
    fun testBroadcast() = CoroutineStart.values().forEach(::testBroadcastCancelledParent)

    private fun testBroadcastCancelledParent(start: CoroutineStart) =
        runTest({ it is CancellationException }) {
            cancel()
            expect(1)
            val bc = broadcast<Int>(start = start) {}
            expect(2)
            (bc as Job).invokeOnCompletion {
                finish(3)
                reset()
            }
        }

    @Test
    fun testScopes() {
        testScope { coroutineScope {  } }
        testScope { supervisorScope {  } }
        testScope { flowScope {  } }
        testScope { withTimeout(Long.MAX_VALUE) {  } }
        testScope { withContext(Job()) {  } }
        testScope { withContext(CoroutineName("")) {  } }
    }

    private inline fun testScope(crossinline block: suspend () -> Unit) = runTest({ it is CancellationException }) {
        cancel()
        block()
    }
}
