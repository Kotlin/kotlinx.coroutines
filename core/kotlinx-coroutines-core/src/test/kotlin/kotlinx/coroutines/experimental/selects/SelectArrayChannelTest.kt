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

package kotlinx.coroutines.experimental.selects

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.channels.*
import kotlinx.coroutines.experimental.intrinsics.*
import org.junit.*
import org.junit.Assert.*
import kotlin.coroutines.experimental.*

class SelectArrayChannelTest : TestBase() {
    @Test
    fun testSelectSendSuccess() = runBlocking<Unit> {
        expect(1)
        val channel = ArrayChannel<String>(1)
        launch(coroutineContext) {
            expect(2)
            assertEquals("OK", channel.receive())
            finish(6)
        }
        yield() // to launched coroutine
        expect(3)
        select<Unit> {
            channel.onSend("OK") {
                expect(4)
            }
        }
        expect(5)
    }

    @Test
    fun testSelectSendSuccessWithDefault() = runBlocking<Unit> {
        expect(1)
        val channel = ArrayChannel<String>(1)
        launch(coroutineContext) {
            expect(2)
            assertEquals("OK", channel.receive())
            finish(6)
        }
        yield() // to launched coroutine
        expect(3)
        select<Unit> {
            channel.onSend("OK") {
                expect(4)
            }
            default {
                expectUnreached()
            }
        }
        expect(5)
    }

    @Test
    fun testSelectSendReceiveBuf() = runBlocking<Unit> {
        expect(1)
        val channel = ArrayChannel<String>(1)
        select<Unit> {
            channel.onSend("OK") {
                expect(2)
            }
        }
        expect(3)
        select<Unit> {
            channel.onReceive { v ->
                expect(4)
                assertEquals("OK", v)
            }
        }
        finish(5)
    }

    @Test
    fun testSelectSendWait() = runBlocking<Unit> {
        expect(1)
        val channel = ArrayChannel<String>(1)
        launch(coroutineContext) {
            expect(4)
            assertEquals("BUF", channel.receive())
            expect(5)
            assertEquals("OK", channel.receive())
            expect(6)
        }
        expect(2)
        channel.send("BUF")
        expect(3)
        select<Unit> {
            channel.onSend("OK") {
                expect(7)
            }
        }
        finish(8)
    }

    @Test
    fun testSelectReceiveSuccess() = runBlocking<Unit> {
        expect(1)
        val channel = ArrayChannel<String>(1)
        channel.send("OK")
        expect(2)
        select<Unit> {
            channel.onReceive { v ->
                expect(3)
                assertEquals("OK", v)
            }
        }
        finish(4)
    }

    @Test
    fun testSelectReceiveSuccessWithDefault() = runBlocking<Unit> {
        expect(1)
        val channel = ArrayChannel<String>(1)
        channel.send("OK")
        expect(2)
        select<Unit> {
            channel.onReceive { v ->
                expect(3)
                assertEquals("OK", v)
            }
            default {
                expectUnreached()
            }
        }
        finish(4)
    }

    @Test
    fun testSelectReceiveWaitWithDefault() = runBlocking<Unit> {
        expect(1)
        val channel = ArrayChannel<String>(1)
        select<Unit> {
            channel.onReceive {
                expectUnreached()
            }
            default {
                expect(2)
            }
        }
        expect(3)
        channel.send("BUF")
        expect(4)
        // make sure second send blocks (select above is over)
        launch(coroutineContext) {
            expect(6)
            channel.send("CHK")
            finish(10)
        }
        expect(5)
        yield()
        expect(7)
        assertEquals("BUF", channel.receive())
        expect(8)
        assertEquals("CHK", channel.receive())
        expect(9)
    }

    @Test
    fun testSelectReceiveWait() = runBlocking<Unit> {
        expect(1)
        val channel = ArrayChannel<String>(1)
        launch(coroutineContext) {
            expect(3)
            channel.send("OK")
            expect(4)
        }
        expect(2)
        select<Unit> {
            channel.onReceive { v ->
                expect(5)
                assertEquals("OK", v)
            }
        }
        finish(6)
    }

    @Test(expected = ClosedReceiveChannelException::class)
    fun testSelectReceiveClosed() = runBlocking<Unit> {
        expect(1)
        val channel = ArrayChannel<String>(1)
        channel.close()
        finish(2)
        select<Unit> {
            channel.onReceive {
                expectUnreached()
            }
        }
        expectUnreached()
    }

    @Test(expected = ClosedReceiveChannelException::class)
    fun testSelectReceiveWaitClosed() = runBlocking<Unit> {
        expect(1)
        val channel = ArrayChannel<String>(1)
        launch(coroutineContext) {
            expect(3)
            channel.close()
            finish(4)
        }
        expect(2)
        select<Unit> {
            channel.onReceive {
                expectUnreached()
            }
        }
        expectUnreached()
    }

    @Test
    fun testSelectSendResourceCleanup() = runBlocking<Unit> {
        val channel = ArrayChannel<Int>(1)
        val n = 10_000_000 * stressTestMultiplier
        expect(1)
        channel.send(-1) // fill the buffer, so all subsequent sends cannot proceed
        repeat(n) { i ->
            select {
                channel.onSend(i) { expectUnreached() }
                default { expect(i + 2) }
            }
        }
        finish(n + 2)
    }

    @Test
    fun testSelectReceiveResourceCleanup() = runBlocking<Unit> {
        val channel = ArrayChannel<Int>(1)
        val n = 10_000_000 * stressTestMultiplier
        expect(1)
        repeat(n) { i ->
            select {
                channel.onReceive { expectUnreached() }
                default { expect(i + 2) }
            }
        }
        finish(n + 2)
    }

    @Test
    fun testSelectReceiveDispatchNonSuspending() = runBlocking<Unit> {
        val channel = ArrayChannel<Int>(1)
        expect(1)
        channel.send(42)
        expect(2)
        launch(coroutineContext) {
            expect(4)
            select<Unit> {
                channel.onReceive { v ->
                    expect(5)
                    assertEquals(42, v)
                    expect(6)
                }
            }
            expect(7) // returns from select without further dispatch
        }
        expect(3)
        yield() // to launched
        finish(8)
    }

    @Test
    fun testSelectReceiveDispatchNonSuspending2() = runBlocking<Unit> {
        val channel = ArrayChannel<Int>(1)
        expect(1)
        channel.send(42)
        expect(2)
        launch(coroutineContext) {
            expect(4)
            select<Unit> {
                channel.onReceive { v ->
                    expect(5)
                    assertEquals(42, v)
                    expect(6)
                    yield() // back to main
                    expect(8)
                }
            }
            expect(9) // returns from select without further dispatch
        }
        expect(3)
        yield() // to launched
        expect(7)
        yield() // again
        finish(10)
    }

    // only for debugging
    internal fun <R> SelectBuilder<R>.default(block: suspend () -> R) {
        this as SelectBuilderImpl // type assertion
        if (!trySelect(null)) return
        block.startCoroutineUndispatched(this)
    }
}