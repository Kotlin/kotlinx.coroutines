/*
 * Copyright 2016-2017 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
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
        run(Schedulers.single().asCoroutineDispatcher()) {
            val t1 = Thread.currentThread()
            println(t1)
            assertThat(t1, IsNot(IsEqual(mainThread)))
            expect(2)
            delay(100)
            val t2 = Thread.currentThread()
            println(t2)
            assertThat(t2, IsNot(IsEqual(mainThread)))
            expect(3)
        }
        finish(4)
    }
}