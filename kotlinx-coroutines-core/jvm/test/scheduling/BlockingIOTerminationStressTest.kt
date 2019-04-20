/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.scheduling.*
import org.junit.*
import java.util.*
import java.util.concurrent.*

class BlockingIOTerminationStressTest : TestBase() {
    private val baseDispatcher = ExperimentalCoroutineDispatcher(
        2, 20,
        TimeUnit.MILLISECONDS.toNanos(10)
    )
    private val ioDispatcher = baseDispatcher.blocking()
    private val TEST_SECONDS = 3L * stressTestMultiplier

    @After
    fun tearDown() {
        baseDispatcher.close()
    }

    @Test
    fun testTermination() {
        val rnd = Random()
        val deadline = System.currentTimeMillis() + TimeUnit.SECONDS.toMillis(TEST_SECONDS)
        while (System.currentTimeMillis() < deadline) {
            Thread.sleep(rnd.nextInt(30).toLong())
            repeat(rnd.nextInt(5) + 1) {
                GlobalScope.launch(ioDispatcher) {
                    Thread.sleep(rnd.nextInt(5).toLong())
                }
            }
        }
    }
}
