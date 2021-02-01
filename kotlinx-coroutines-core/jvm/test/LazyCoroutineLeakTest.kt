/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.channels.*
import org.junit.*

class LazyCoroutineLeakTest : TestBase() {

    private object NonReachable

    private fun capturingBlock(victim: Any): suspend CoroutineScope.() -> Unit = { victim.hashCode() }

    private suspend fun Job.testStartAndJoin() {
        FieldWalker.assertReachableCount(1, this) { it === NonReachable }
        start()
        join()
        FieldWalker.assertReachableCount(0, this) { it === NonReachable }
    }

    suspend fun Job.testCancelAndJoin() {
        FieldWalker.assertReachableCount(1, this) { it === NonReachable }
        cancelAndJoin()
        FieldWalker.assertReachableCount(0, this) { it === NonReachable }
    }

    @Test
    fun testLazyLaunch() = runTest {
        launch(start = CoroutineStart.LAZY, block = capturingBlock(NonReachable)).testStartAndJoin()
    }

    @Test
    fun testLazyLaunchCancel() = runTest {
        launch(start = CoroutineStart.LAZY, block = capturingBlock(NonReachable)).testCancelAndJoin()

    }

    @Test
    fun testLazyAsync() = runTest {
        async(start = CoroutineStart.LAZY, block = capturingBlock(NonReachable)).testStartAndJoin()
    }

    @Test
    fun testLazyLaunchAsync() = runTest {
        async(start = CoroutineStart.LAZY, block = capturingBlock(NonReachable)).testCancelAndJoin()
    }

    @Test
    fun testLazyActor() = runTest {
        (actor<Int>(start = CoroutineStart.LAZY, block = capturingBlock(NonReachable)) as Job).testStartAndJoin()
    }

    @Test
    fun testLazyActorCancel() = runTest {
        (actor<Int>(start = CoroutineStart.LAZY, block = capturingBlock(NonReachable)) as Job).testCancelAndJoin()
    }

    // Lazy produce & future are not supported, broadcast is obsolete
}
