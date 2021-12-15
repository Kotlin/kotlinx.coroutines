/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlin.test.*
import kotlin.time.*
import kotlin.time.Duration.Companion.milliseconds
import kotlin.time.Duration.Companion.seconds

@kotlin.time.ExperimentalTime
class SharingStartedWhileSubscribedTest : TestBase() {
    @Test // make sure equals works properly, or otherwise other tests don't make sense
    fun testEqualsAndHashcode() {
        val params = listOf(0L, 1L, 10L, 100L, 213L, Long.MAX_VALUE)
        // HashMap will simultaneously test equals, hashcode and their consistency
        val map = HashMap<SharingStarted, Pair<Long, Long>>()
        for (i in params) {
            for (j in params) {
                map[SharingStarted.WhileSubscribed(i, j)] = i to j
            }
        }
        for (i in params) {
            for (j in params) {
                assertEquals(i to j, map[SharingStarted.WhileSubscribed(i, j)])
            }
        }
    }

    @Test
    fun testDurationParams() {
        assertEquals(SharingStarted.WhileSubscribed(0), SharingStarted.WhileSubscribed(Duration.ZERO))
        assertEquals(SharingStarted.WhileSubscribed(10), SharingStarted.WhileSubscribed(10.milliseconds))
        assertEquals(SharingStarted.WhileSubscribed(1000), SharingStarted.WhileSubscribed(Duration.seconds(1)))
        assertEquals(SharingStarted.WhileSubscribed(Long.MAX_VALUE), SharingStarted.WhileSubscribed(Duration.INFINITE))
        assertEquals(SharingStarted.WhileSubscribed(replayExpirationMillis = 0), SharingStarted.WhileSubscribed(replayExpiration = Duration.ZERO))
        assertEquals(SharingStarted.WhileSubscribed(replayExpirationMillis = 3), SharingStarted.WhileSubscribed(
            replayExpiration = 3.milliseconds
        ))
        assertEquals(SharingStarted.WhileSubscribed(replayExpirationMillis = 7000),
            SharingStarted.WhileSubscribed(replayExpiration = Duration.seconds(7)
        ))
        assertEquals(SharingStarted.WhileSubscribed(replayExpirationMillis = Long.MAX_VALUE), SharingStarted.WhileSubscribed(replayExpiration = Duration.INFINITE))
    }

    @Test
    fun testShouldRestart() = runTest {
        var started = 0
        val flow = flow {
            expect(1 + ++started)
            emit(1)
            hang {  }
        }.shareIn(this, SharingStarted.WhileSubscribed(100 /* ms */))

        expect(1)
        flow.first()
        delay(200)
        flow.first()
        finish(4)
        coroutineContext.job.cancelChildren()
    }

    @Test
    fun testImmediateUnsubscribe() = runTest {
        val flow = flow {
            expect(2)
            emit(1)
            hang { finish(4) }
        }.shareIn(this, SharingStarted.WhileSubscribed(400, 0 /* ms */), 1)

        expect(1)
        repeat(5) {
            flow.first()
            delay(100)
        }
        expect(3)
        coroutineContext.job.cancelChildren()
    }
}
