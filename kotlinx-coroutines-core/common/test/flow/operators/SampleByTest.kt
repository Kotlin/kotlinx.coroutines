/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow.operators

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.flow.*
import kotlin.test.*

class SampleByTest : TestBase() {
    @Test
    public fun testBasicWithFlow() = withVirtualTime {
        expect(1)
        val flow = flow {
            expect(3)
            delay(200)
            emit("A")
            expect(4)
            delay(600)
            emit("B")
            delay(200)
            emit("C")
            delay(200)
            expect(6)
            emit("D")
            delay(10000)
            expect(7)
        }


        val samplerFlow = flow {
            delay(1000)
            expect(5)
            emit("AA")
            delay(1000)
            emit("BB")
        }
        expect(2)
        val result = flow.sampleBy(samplerFlow).toList()
        assertEquals(listOf("B", "D"), result)
        finish(8)
    }
    @Test
    fun testDelayedFirstWithFlow() = withVirtualTime {
        val flow = flow {
            delay(60)
            emit(1)
            expect(1)
            delay(60)
            expect(3)
        }.sampleBy(flow {
            delay(100)
            emit(4)
            expect(2)
        })
        assertEquals(1, flow.singleOrNull())
        finish(4)
    }


    @Test
    fun testBasicFlow2() = withVirtualTime {
        expect(1)
        val flow = flow {
            expect(3)
            emit(1)
            emit(2)
            delay(501)
            emit(3)
            delay(100)
            emit(4)
            delay(100)
            emit(5)
            emit(6)
            delay(301)
            emit(7)
            delay(501)
            expect(4)
        }
        val samplerFlow = flow {
            delay(500)
            repeat(10) {
                emit(1)
                delay(500)
            }
        }
        expect(2)
        val result = flow.sampleBy(samplerFlow).toList()
        assertEquals(listOf(2, 6, 7), result)
        finish(5)
    }

    @Test
    fun testFixedDelayWithFlow() = withVirtualTime {
        val flow = flow {
            emit("A")
            expect(1)
            delay(150)
            emit("B")
            expect(3)
        }.sampleBy(flow {
            delay(100)
            emit("A")
            expect(2)
        })
        assertEquals("A", flow.single())
        finish(4)
    }

    @Test
    fun testSingleNullWithFlow() = withVirtualTime {
        val flow = flow<Int?> {
            emit(null)
            delay(2)
            expect(1)
        }.sampleBy(flow {
            delay(1)
            emit(1)
        })
        assertNull(flow.single())
        finish(2)
    }

    @Test
    fun testBasicWithNullsWithFlow() = withVirtualTime {
        expect(1)
        val flow = flow {
            expect(3)
            emit("A")
            delay(1500)
            emit(null)
            delay(500)
            emit("C")
            delay(250)
            emit(null)
            delay(2000)
            emit("E")
            expect(4)
        }

        expect(2)
        val sampler = flow {
            repeat(20) {
                delay(1000)
                repeat(10) {
                    emit(1)
                    delay(1000)
                }
            }
        }
        val result = flow.sampleBy(sampler).toList()
        assertEquals(listOf("A", null, null), result)
        finish(5)
    }

    @Test
    fun testEmptyWithFlow() = runTest {
        val flow = emptyFlow<Int>().sampleBy(flow {
            delay(Long.MAX_VALUE)
            emit(1)
        })
        assertNull(flow.singleOrNull())
    }

    @Test
    fun testScalarWithFlow() = runTest {
        val flow = flowOf(1, 2, 3).sampleBy(flow {
            delay(Long.MAX_VALUE)
            emit(1)
        })
        assertNull(flow.singleOrNull())
    }

    @Test
    // note that this test depends on the sampling strategy -- when sampling time starts on a quiescent flow that suddenly emits
    fun testLongWaitWithFlow() = withVirtualTime {
        expect(1)
        val flow = flow {
            expect(2)
            emit("A")
            delay(3500) // long delay -- multiple sampling intervals
            emit("B")
            delay(900) // crosses time = 4000 barrier
            emit("C")
            delay(3000) // long wait again

        }
        val result = flow.sampleBy(flow {
            repeat(10){
                delay(1000)
                emit(1)
            }
        }).toList()
        assertEquals(listOf("A", "B", "C"), result)
        finish(3)
    }

    @Test
    fun testPaceWithFlow() = withVirtualTime {
        val flow = flow {
            expect(1)
            repeat(4) {
                emit(-it)
                delay(50)
            }

            repeat(4) {
                emit(it)
                delay(100)
            }
            expect(2)
        }.sampleBy( flow {
            repeat(10) {
                delay(100)
                emit(1)
            }
        })

        assertEquals(listOf(-1, -3, 0, 1, 2, 3), flow.toList())
        finish(3)

    }

    @Test
    fun testUpstreamErrorWithFlow() = runTest {
        val latch = Channel<Unit>()
        val flow = flow {
            expect(1)
            emit(1)
            expect(2)
            latch.receive()
            throw TestException()
        }.sampleBy(flow {
            repeat(10) {
                delay(1)
                emit(1)
            }
        }).map {
            latch.send(Unit)
            hang { expect(3) }
        }

        assertFailsWith<TestException>(flow)
        finish(4)
    }

    @Test
    fun testUpstreamErrorIsolatedContextWithFlow() = runTest {
        val latch = Channel<Unit>()
        val flow = flow {
            assertEquals("upstream", NamedDispatchers.name())
            expect(1)
            emit(1)
            expect(2)
            latch.receive()
            throw TestException()
        }.flowOn(NamedDispatchers("upstream")).sampleBy(flow {
            repeat(10) {
                delay(1)
                emit(1)
            }
        }).map {
            latch.send(Unit)
            hang { expect(3) }
        }

        assertFailsWith<TestException>(flow)
        finish(4)
    }

    @Test
    fun testUpstreamErrorSampleNotTriggeredWithFlow() = runTest {
        val flow = flow {
            expect(1)
            emit(1)
            expect(2)
            throw TestException()
        }.sampleBy(flow{
            delay(Long.MAX_VALUE)
            emit(1)
        }).map {
            expectUnreached()
        }
        assertFailsWith<TestException>(flow)
        finish(3)
    }

    @Test
    fun testUpstreamErrorSampleNotTriggeredInIsolatedContextWithFlow() = runTest {
        val flow = flow {
            expect(1)
            emit(1)
            expect(2)
            throw TestException()
        }.flowWith(NamedDispatchers("unused")) {
            sampleBy(flow{
                delay(Long.MAX_VALUE)
                emit(1)
            }).map {
                expectUnreached()
            }
        }

        assertFailsWith<TestException>(flow)
        finish(3)
    }

    @Test
    fun testDownstreamErrorWithFlow() = runTest {
        val flow = flow {
            expect(1)
            emit(1)
            hang { expect(3) }
        }.sampleBy(flow {
            repeat(100) {
                delay(1)
                emit(1)
            }
        }).map {
            expect(2)
            yield()
            throw TestException()
            it
        }

        assertFailsWith<TestException>(flow)
        finish(4)
    }

    @Test
    fun testDownstreamErrorIsolatedContextWithFlow() = runTest {
        val flow = flow {
            assertEquals("upstream", NamedDispatchers.name())
            expect(1)
            emit(1)
            hang { expect(3) }
        }.flowOn(NamedDispatchers("upstream")).sampleBy(flow {
            repeat(100) {
                delay(1)
                emit(1)
            }
        }).map {
            expect(2)
            yield()
            throw TestException()
            it
        }

        assertFailsWith<TestException>(flow)
        finish(4)
    }
}
