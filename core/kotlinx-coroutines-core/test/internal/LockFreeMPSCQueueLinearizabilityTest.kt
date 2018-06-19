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

package kotlinx.coroutines.experimental.internal

import com.devexperts.dxlab.lincheck.*
import com.devexperts.dxlab.lincheck.annotations.*
import com.devexperts.dxlab.lincheck.paramgen.*
import com.devexperts.dxlab.lincheck.stress.*
import kotlinx.coroutines.experimental.*
import kotlin.test.*

@OpGroupConfigs(OpGroupConfig(name = "consumer", nonParallel = true))
@Param(name = "value", gen = IntGen::class, conf = "1:3")
class LockFreeMPSCQueueLinearizabilityTest : TestBase() {
    private lateinit var q: LockFreeMPSCQueue<Int>

    @Reset
    fun reset() {
        q = LockFreeMPSCQueue()
    }

    @Operation
    fun close() = q.close()

    @Operation
    fun addLast(@Param(name = "value") value: Int) = q.addLast(value)

    /**
     * Note, that removeFirstOrNull is not linearizable w.r.t. to addLast, so here
     * we test only linearizability of close.
     */
//    @Operation(group = "consumer")
//    fun removeFirstOrNull() = q.removeFirstOrNull()

    @Test
    fun testLinearizability() {
        val options = StressOptions()
            .iterations(100 * stressTestMultiplierSqrt)
            .invocationsPerIteration(1000 * stressTestMultiplierSqrt)
            .addThread(1, 3)
            .addThread(1, 3)
            .addThread(1, 3)
        LinChecker.check(LockFreeMPSCQueueLinearizabilityTest::class.java, options)
    }
}