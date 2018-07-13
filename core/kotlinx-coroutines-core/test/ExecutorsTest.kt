/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

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