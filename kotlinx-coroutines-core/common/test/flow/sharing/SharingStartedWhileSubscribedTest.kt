/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlin.test.*
import kotlin.time.*

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

    @OptIn(ExperimentalTime::class)
    @Test
    fun testDurationParams() {
        assertEquals(SharingStarted.WhileSubscribed(0), SharingStarted.WhileSubscribed(Duration.ZERO))
        assertEquals(SharingStarted.WhileSubscribed(10), SharingStarted.WhileSubscribed(10.milliseconds))
        assertEquals(SharingStarted.WhileSubscribed(1000), SharingStarted.WhileSubscribed(1.seconds))
        assertEquals(SharingStarted.WhileSubscribed(Long.MAX_VALUE), SharingStarted.WhileSubscribed(Duration.INFINITE))
        assertEquals(SharingStarted.WhileSubscribed(replayExpirationMillis = 0), SharingStarted.WhileSubscribed(replayExpiration = Duration.ZERO))
        assertEquals(SharingStarted.WhileSubscribed(replayExpirationMillis = 3), SharingStarted.WhileSubscribed(replayExpiration = 3.milliseconds))
        assertEquals(SharingStarted.WhileSubscribed(replayExpirationMillis = 7000), SharingStarted.WhileSubscribed(replayExpiration = 7.seconds))
        assertEquals(SharingStarted.WhileSubscribed(replayExpirationMillis = Long.MAX_VALUE), SharingStarted.WhileSubscribed(replayExpiration = Duration.INFINITE))
    }
}

