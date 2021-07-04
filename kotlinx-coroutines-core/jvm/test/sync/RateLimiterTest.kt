/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.sync

import kotlin.test.assertEquals
import kotlin.time.Duration
import kotlin.time.ExperimentalTime
import kotlinx.coroutines.runBlocking
import kotlinx.coroutines.test.*
import kotlinx.coroutines.time.*
import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.Parameterized
import org.junit.runners.Parameterized.Parameters

@RunWith(Parameterized::class)
@OptIn(ExperimentalTime::class)
class RateLimiterTest(private val eventsPerInterval: Int) {

    companion object {

        @JvmStatic
        @Parameters(name="{0} events per interval")
        fun data(): Collection<Array<Any>> = listOf(1, 3, 10, 100, 1000).map { arrayOf(it) }
    }

    @Test
    fun acquire(): Unit = runBlocking {
        val delayer = Delayer()
        val timeSource: NanoTimeSource = TestNanoTimeSource()
        val rateLimiter = RateLimiterImpl(
            eventsPerInterval = eventsPerInterval,
            interval = Duration.seconds(1),
            timeSource = timeSource,
            delay = delayer::delay
        )
        (0..eventsPerInterval).forEach { delayMultiplier ->
            delayer.reset()
            rateLimiter.acquire()
            val delaySum = delayer.getDelay()
            val expectedDelay: Long = (1000L / eventsPerInterval) * delayMultiplier
            assertEquals(
                expectedDelay, delaySum,
                "Failed for eventsPerInterval: $eventsPerInterval round #$delayMultiplier took $delaySum ms"
            )
        }
    }
}
