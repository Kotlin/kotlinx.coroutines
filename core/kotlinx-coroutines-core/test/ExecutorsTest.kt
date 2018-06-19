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

package kotlinx.coroutines.experimental

import org.junit.Test
import java.util.concurrent.Executors

class ExecutorsTest : TestBase() {
    fun checkThreadName(prefix: String) {
        val name = Thread.currentThread().name
        check(name.startsWith(prefix)) { "Expected thread name to start with '$prefix', found: '$name'" }
    }

    @Test
    fun testSingleThread() {
        val context = newSingleThreadContext("TestThread")
        runBlocking(context) {
            checkThreadName("TestThread")
        }
        context.close()
    }

    @Test
    fun testFixedThreadPool() {
        val context = newFixedThreadPoolContext(2, "TestPool")
        runBlocking(context) {
            checkThreadName("TestPool")
        }
        context.close()
    }

    @Test
    fun testToExecutor() {
        val executor = Executors.newSingleThreadExecutor { r -> Thread(r, "TestExecutor") }
        runBlocking(executor.asCoroutineDispatcher()) {
            checkThreadName("TestExecutor")
        }
        executor.shutdown()
    }

    @Test
    fun testTwoThreads() {
        val ctx1 = newSingleThreadContext("Ctx1")
        val ctx2 = newSingleThreadContext("Ctx2")
        runBlocking(ctx1) {
            checkThreadName("Ctx1")
            withContext(ctx2) {
                checkThreadName("Ctx2")
            }
            checkThreadName("Ctx1")
        }
        ctx1.close()
        ctx2.close()
    }

    @Test
    fun testShutdownExecutorService() {
        val executorService = Executors.newSingleThreadExecutor { r -> Thread(r, "TestExecutor") }
        val dispatcher = executorService.asCoroutineDispatcher()
        runBlocking (dispatcher) {
            checkThreadName("TestExecutor")
        }
        dispatcher.close()
        check(executorService.isShutdown)
    }
}