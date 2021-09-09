/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import org.junit.Test
import java.util.concurrent.*
import kotlin.coroutines.*
import kotlin.test.*

class ExecutorsTest : TestBase() {
    private fun checkThreadName(prefix: String) {
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
            delay(10)
            checkThreadName("TestPool") // should dispatch on the right thread
        }
        context.close()
    }

    @Test
    fun testExecutorToDispatcher() {
        val executor = Executors.newSingleThreadExecutor { r -> Thread(r, "TestExecutor") }
        runBlocking(executor.asCoroutineDispatcher()) {
            checkThreadName("TestExecutor")
            delay(10)
            checkThreadName("TestExecutor") // should dispatch on the right thread
        }
        executor.shutdown()
    }

    @Test
    fun testConvertedDispatcherToExecutor() {
        val executor: ExecutorService = Executors.newSingleThreadExecutor { r -> Thread(r, "TestExecutor") }
        val dispatcher: CoroutineDispatcher = executor.asCoroutineDispatcher()
        assertSame(executor, dispatcher.asExecutor())
        executor.shutdown()
    }

    @Test
    fun testDefaultDispatcherToExecutor() {
        val latch = CountDownLatch(1)
        Dispatchers.Default.asExecutor().execute {
            checkThreadName("DefaultDispatcher")
            latch.countDown()
        }
        latch.await()
    }

    @Test
    fun testCustomDispatcherToExecutor() {
        expect(1)
        val dispatcher = object : CoroutineDispatcher() {
            override fun dispatch(context: CoroutineContext, block: Runnable) {
                expect(2)
                block.run()
            }
        }
        val executor = dispatcher.asExecutor()
        assertSame(dispatcher, executor.asCoroutineDispatcher())
        executor.execute {
            expect(3)
        }
        finish(4)
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