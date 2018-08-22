/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.rx1

import kotlinx.coroutines.experimental.*
import org.hamcrest.core.IsEqual
import org.hamcrest.core.IsNot
import org.junit.Assert.assertThat
import org.junit.Before
import org.junit.Test
import rx.schedulers.Schedulers

class SchedulerTest : TestBase() {
    @Before
    fun setup() {
        ignoreLostThreads("RxIoScheduler-")
    }

    @Test
    fun testIoScheduler(): Unit = runBlocking {
        expect(1)
        val mainThread = Thread.currentThread()
        withContext(Schedulers.io().asCoroutineDispatcher()) {
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