/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.scheduling

import kotlinx.atomicfu.*
import kotlinx.coroutines.experimental.*
import org.junit.Test
import java.util.*
import kotlin.test.*

class CoroutineSchedulerCloseStressTest : TestBase() {
    private val N_REPEAT = 2 * stressTestMultiplier
    private val MAX_LEVEL = 5
    private val N_COROS = (1 shl (MAX_LEVEL + 1)) - 1
    private val N_THREADS = 4
    private val rnd = Random()

    private lateinit var dispatcher: ExecutorCoroutineDispatcher
    private var closeIndex = -1

    private val started = atomic(0)
    private val finished = atomic(0)

    @Test
    fun testNormalClose() {
        try {
            launchCoroutines()
        } finally {
            dispatcher.close()
        }
    }

    @Test
    fun testRacingClose() {
        repeat(N_REPEAT) {
            closeIndex = rnd.nextInt(N_COROS)
            launchCoroutines()
        }
    }

    private fun launchCoroutines() = runBlocking {
        dispatcher = ExperimentalCoroutineDispatcher(N_THREADS)
        started.value = 0
        finished.value = 0
        withContext(dispatcher) {
            launchChild(0, 0)
        }
        assertEquals(N_COROS, started.value)
        assertEquals(N_COROS, finished.value)
    }

    private fun CoroutineScope.launchChild(index: Int, level: Int): Job = launch(start = CoroutineStart.ATOMIC) {
        started.incrementAndGet()
        try {
            if (index == closeIndex) dispatcher.close()
            if (level < MAX_LEVEL) {
                launchChild(2 * index + 1, level + 1)
                launchChild(2 * index + 2, level + 1)
            } else {
                delay(1000)
            }
        } finally {
            finished.incrementAndGet()
        }
    }
}