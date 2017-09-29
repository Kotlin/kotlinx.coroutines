/*
 * Copyright 2016-2017 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package kotlinx.coroutines.experimental.channels

import kotlinx.coroutines.experimental.*
import org.junit.Test

class DoubleChannelCloseStressTest : TestBase() {
    val nTimes = 1000 * stressTestMultiplier

    @Test
    fun testDoubleCloseStress() {
        repeat(nTimes) {
            val actor = actor<Int>(CommonPool + CoroutineName("actor"), start = CoroutineStart.LAZY) {
                // empty -- just closes channel
            }
            launch(CommonPool + CoroutineName("sender")) {
                actor.send(1)
            }
            Thread.sleep(1)
            actor.close()
        }
    }
}