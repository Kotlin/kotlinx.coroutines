/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.reactor

import kotlinx.coroutines.experimental.*
import org.hamcrest.core.IsEqual
import org.hamcrest.core.IsNot
import org.junit.Assert.assertThat
import org.junit.Before
import org.junit.Test
import reactor.core.scheduler.Schedulers

class SchedulerTest : TestBase() {
    @Before
    fun setup() {
        ignoreLostThreads("single-")
    }

    @Test
    fun testSingleScheduler(): Unit = runBlocking {
        expect(1)
        val mainThread = Thread.currentThread()
        withContext(Schedulers.single().asCoroutineDispatcher()) {
            val t1 = Thread.currentThread()
            assertThat(t1, IsNot(IsEqual(mainThread)))
            expect(2)
            delay(100)
            val t2 = Thread.currentThread()
            assertThat(t2, IsNot(IsEqual(mainThread)))
            expect(3)
        }
        finish(4)
    }
}