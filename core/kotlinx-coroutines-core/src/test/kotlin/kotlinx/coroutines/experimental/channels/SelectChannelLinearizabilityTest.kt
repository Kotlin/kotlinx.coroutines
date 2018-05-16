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

import com.devexperts.dxlab.lincheck.*
import com.devexperts.dxlab.lincheck.annotations.*
import com.devexperts.dxlab.lincheck.paramgen.*
import com.devexperts.dxlab.lincheck.stress.*
import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.selects.*
import org.junit.*
import java.io.*

@Param(name = "value", gen = IntGen::class, conf = "1:3")
class SelectChannelLinearizabilityTest : TestBase() {

    private val lt = LinTesting()
    private var capacity = 0
    private lateinit var channel: Channel<Int>

    @Reset
    fun reset() {
        channel = Channel(capacity)
    }

    @Operation(runOnce = true)
    fun onSend1(@Param(name = "value") value: Int) = onSend(value, "onSend1")

    @Operation(runOnce = true)
    fun onSend2(@Param(name = "value") value: Int) = onSend(value, "onSend2")


    private fun onSend(value: Int, name: String): List<OpResult> {
        return lt.run(name) {
            select<Unit> {
                channel.onSend(value) {}
            }
        }
    }

    @Operation(runOnce = true)
    fun close1() = lt.run("close1") { channel.close(IOException("close1")) }

    @Operation(runOnce = true)
    fun close2() = lt.run("close2") { channel.close(IOException("close2")) }

    @Operation(runOnce = true)
    fun onReceive1() = onReceive("onReceive1")

    @Operation(runOnce = true)
    fun onReceive2() = onReceive("onReceive2")

    private fun onReceive(name: String): List<OpResult> {
        return lt.run(name) {
            select<Int> {
                channel.onReceive {
                    it
                }
            }
        }
    }

    @Operation(runOnce = true)
    fun onClose1() = onClose("onClose1")

    @Operation(runOnce = true)
    fun onClose2() = onClose("onClose2")

    private fun onClose(name: String): List<OpResult> {
        return lt.run(name) {
            select<Unit> {
                channel.onClose {
                    try {
                        val result = channel.offer(42)
                        throw AssertionError("Offer in 'onClose' should throw, but instead returned $result")
                    } catch (e: Exception) {
                        // Should happen
                    }
                }
            }
        }
    }

    @Test
    fun testRendezvousChannelLinearizability() {
        runTest(0)
    }

    @Test
    fun testArrayChannelLinearizability() {
        for (i in listOf(1, 2, 16)) {
            runTest(i)
        }
    }

    @Test
    fun testConflatedChannelLinearizability() = runTest(Channel.CONFLATED)

    @Test
    fun testUnlimitedChannelLinearizability() = runTest(Channel.UNLIMITED)

    private fun runTest(capacity: Int) {
        this.capacity = capacity
        val options = StressOptions()
            .iterations(100)
            .invocationsPerIteration(200 * stressTestMultiplier)
            .addThread(1, 3)
            .addThread(1, 3)
            .addThread(1, 3)
            .addThread(1, 3)
            .verifier(LinVerifier::class.java)
        LinChecker.check(SelectChannelLinearizabilityTest::class.java, options)
    }
}
