/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("DeferredResultUnused")

package kotlinx.coroutines

import kotlinx.coroutines.channels.*
import org.junit.*
import org.junit.Test
import org.junit.rules.*
import kotlin.test.*

class FailFastOnStartTest : TestBase() {

    @Rule
    @JvmField
    public val timeout: Timeout = Timeout.seconds(5)

    @Test
    fun testLaunch() = runTest(expected = ::mainException) {
        launch(Dispatchers.Main) {}
    }

    @Test
    fun testLaunchLazy() = runTest(expected = ::mainException) {
        val job = launch(Dispatchers.Main, start = CoroutineStart.LAZY) { fail() }
        job.join()
    }

    @Test
    fun testLaunchUndispatched() = runTest(expected = ::mainException) {
        launch(Dispatchers.Main, start = CoroutineStart.UNDISPATCHED) {
            yield()
            fail()
        }
    }

    @Test
    fun testAsync() = runTest(expected = ::mainException) {
        async(Dispatchers.Main) {}
    }

    @Test
    fun testAsyncLazy() = runTest(expected = ::mainException) {
        val job = async(Dispatchers.Main, start = CoroutineStart.LAZY) { fail() }
        job.await()
    }

    @Test
    fun testWithContext() = runTest(expected = ::mainException) {
        withContext(Dispatchers.Main) {
            fail()
        }
    }

    @Test
    fun testProduce() = runTest(expected = ::mainException) {
        produce<Int>(Dispatchers.Main) { fail() }
    }

    @Test
    fun testActor() = runTest(expected = ::mainException) {
        actor<Int>(Dispatchers.Main) { fail() }
    }

    @Test
    fun testActorLazy() = runTest(expected = ::mainException) {
        val actor = actor<Int>(Dispatchers.Main, start = CoroutineStart.LAZY) { fail() }
        actor.send(1)
    }
    
    private fun mainException(e: Throwable): Boolean {
        return e is IllegalStateException && e.message?.contains("Module with the Main dispatcher is missing") ?: false
    }
}
