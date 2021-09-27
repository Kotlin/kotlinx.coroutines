/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.scheduling

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import org.junit.Test
import org.junit.runner.*
import org.junit.runners.*
import java.util.*
import kotlin.test.*

@RunWith(Parameterized::class)
class CoroutineSchedulerCloseStressTest(private val mode: Mode) : TestBase() {
    enum class Mode { CPU, BLOCKING, CPU_LIMITED }

    companion object {
        @Parameterized.Parameters(name = "mode={0}")
        @JvmStatic
        fun params(): Collection<Array<Any>> = Mode.values().map { arrayOf<Any>(it) }
    }

    private val MAX_LEVEL = 5
    private val N_COROS = (1 shl (MAX_LEVEL + 1)) - 1
    private val N_THREADS = 4
    private val rnd = Random()

    private lateinit var closeableDispatcher: SchedulerCoroutineDispatcher
    private lateinit var dispatcher: CoroutineDispatcher

    private val started = atomic(0)
    private val finished = atomic(0)

    @Test
    fun testNormalClose() {
        try {
            launchCoroutines()
        } finally {
            closeableDispatcher.close()
        }
    }

    private fun launchCoroutines() = runBlocking {
        closeableDispatcher = SchedulerCoroutineDispatcher(N_THREADS)
        dispatcher = when (mode) {
            Mode.CPU -> closeableDispatcher
            Mode.CPU_LIMITED -> closeableDispatcher.limitedParallelism(N_THREADS)
            Mode.BLOCKING -> closeableDispatcher.blocking(N_THREADS)
        }
        started.value = 0
        finished.value = 0
        withContext(dispatcher) {
            launchChild(0, 0)
        }
        assertEquals(N_COROS, started.value)
        assertEquals(N_COROS, finished.value)
    }

    // Index and level are used only for debugging purpose
    private fun CoroutineScope.launchChild(index: Int, level: Int): Job = launch(start = CoroutineStart.ATOMIC) {
        started.incrementAndGet()
        try {
            if (level < MAX_LEVEL) {
                launchChild(2 * index + 1, level + 1)
                launchChild(2 * index + 2, level + 1)
            } else {
                if (rnd.nextBoolean()) {
                    delay(1000)
                } else {
                    yield()
                }
            }
        } finally {
            finished.incrementAndGet()
        }
    }
}
