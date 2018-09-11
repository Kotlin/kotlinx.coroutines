/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.channels

import kotlinx.coroutines.experimental.*
import org.junit.*

class DoubleChannelCloseStressTest : TestBase() {
    private val nTimes = 1000 * stressTestMultiplier

    @Test
    fun testDoubleCloseStress() {
        repeat(nTimes) {
            val actor = GlobalScope.actor<Int>(CoroutineName("actor"), start = CoroutineStart.LAZY) {
                // empty -- just closes channel
            }
            GlobalScope.launch(CoroutineName("sender")) {
                actor.send(1)
            }
            Thread.sleep(1)
            actor.close()
        }
    }
}
