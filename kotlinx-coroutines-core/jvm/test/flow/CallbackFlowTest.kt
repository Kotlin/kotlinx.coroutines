/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import org.junit.Test
import kotlin.concurrent.*
import kotlin.test.*

class CallbackFlowTest : TestBase() {

    private class CallbackApi(val block: (SendChannel<Int>) -> Unit) {
        var started = false
        @Volatile
        var stopped = false
        lateinit var thread: Thread

        fun start(sink: SendChannel<Int>) {
            started = true
            thread = thread {
                while (!stopped) {
                    block(sink)
                }
            }
        }

        fun stop() {
            stopped = true
        }
    }

    @Test(timeout = 5_000L)
    fun testThrowingConsumer() = runTest {
        var i = 0
        val api = CallbackApi {
            runCatching {  it.offer(++i) }
        }

        val flow = channelFlow<Int> {
            api.start(channel)
            awaitClose {
                api.stop()
            }
        }

        var receivedConsensus = 0
        var isDone = false
        var exception: Throwable? = null
        val job = flow
            .filter { it > 10 }
            .launchIn(this) {
                onEach {
                    if (it == 11) {
                        ++receivedConsensus
                    } else {
                        receivedConsensus = 42
                    }
                    throw RuntimeException()
                }
                catch<Throwable> { exception = it }
                finally { isDone = true }
            }
        job.join()
        assertEquals(1, receivedConsensus)
        assertTrue(isDone)
        assertTrue { exception is RuntimeException }
        api.thread.join()
        assertTrue(api.started)
        assertTrue(api.stopped)
    }

    @Test(timeout = 5_000L)
    fun testThrowingSource() = runBlocking {
        var i = 0
        val api = CallbackApi {
            if (i < 5) {
                it.offer(++i)
            } else {
                it.close(RuntimeException())
            }
        }

        val flow = callbackFlow<Int>() {
            api.start(channel)
            awaitClose {
                api.stop()
            }
        }

        var received = 0
        var isDone = false
        var exception: Throwable? = null
        val job = flow.launchIn(this) {
            onEach { ++received }
            catch<Throwable> { exception = it }
            finally { isDone = true }
        }

        job.join()
        assertTrue(isDone)
        assertTrue { exception is RuntimeException }
        api.thread.join()
        assertTrue(api.started)
        assertTrue(api.stopped)
    }


    @Test
    fun testMergeExample() = runTest {
        // Too slow on JS
        withContext(Dispatchers.Default) {
            val f1 = (1..10_000).asFlow()
            val f2 = (10_001..20_000).asFlow()
            assertEquals((1..20_000).toSet(), f1.merge(f2).toSet())
        }
    }

    private fun Flow<Int>.merge(other: Flow<Int>): Flow<Int> = callbackFlow {
        launch {
            collect { send(it) }
        }
        other.collect { send(it) }
    }
}
