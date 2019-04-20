/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlin.coroutines.*
import kotlin.test.*

class FlowContextTest : TestBase() {

    private val captured = ArrayList<String>()

    @Test
    fun testMixedContext() = runTest {
        val flow = flow {
            captured += NamedDispatchers.nameOr("main")
            emit(314)
        }

        val mapper: suspend (Int) -> Int = {
            captured += NamedDispatchers.nameOr("main")
            it
        }

        val value = flow // upstream
            .map(mapper) // upstream
            .flowOn(NamedDispatchers("upstream"))
            .map(mapper) // upstream 2
            .flowWith(NamedDispatchers("downstream")) {
                map(mapper) // downstream
            }
            .flowOn(NamedDispatchers("upstream 2"))
            .map(mapper) // main
            .single()

        assertEquals(314, value)
        assertEquals(listOf("upstream", "upstream", "upstream 2", "downstream", "main"), captured)
    }

    @Test
    fun testException() = runTest {
        val flow = flow {
            emit(314)
            delay(Long.MAX_VALUE)
        }.flowOn(NamedDispatchers("upstream"))
            .map {
                throw TestException()
            }

        assertFailsWith<TestException> { flow.single() }
        assertFailsWith<TestException>(flow)
        ensureActive()
    }

    @Test
    fun testMixedContextsAndException() = runTest {
        val baseFlow = flow {
            emit(314)
            hang { }
        }

        var state = 0
        var needle = 1
        val mapper: suspend (Int) -> Int = {
            if (++state == needle) throw TestException()
            it
        }

        val flow = baseFlow.map(mapper) // 1
            .flowOn(NamedDispatchers("ctx 1"))
            .map(mapper) // 2
            .flowWith(NamedDispatchers("ctx 2")) {
                map(mapper) // 3
            }
            .map(mapper) // 4
            .flowOn(NamedDispatchers("ctx 3"))
            .map(mapper) // 5

        repeat(5) {  // Will hang for 6
            state = 0
            needle = it + 1
            assertFailsWith<TestException> { flow.single() }

            state = 0
            assertFailsWith<TestException>(flow)
        }

        ensureActive()
    }

    @Test
    fun testNestedContexts() = runTest {
        val mapper: suspend (Int) -> Int = { captured += NamedDispatchers.nameOr("main"); it }
        val value = flow {
            captured += NamedDispatchers.nameOr("main")
            emit(1)
        }.flowWith(NamedDispatchers("outer")) {
            map(mapper)
                .flowOn(NamedDispatchers("nested first"))
                .flowWith(NamedDispatchers("nested second")) {
                    map(mapper)
                        .flowOn(NamedDispatchers("inner first"))
                        .map(mapper)
                }
                .map(mapper)
        }.map(mapper)
            .single()

        val expected = listOf("main", "nested first", "inner first", "nested second", "outer", "main")
        assertEquals(expected, captured)
        assertEquals(1, value)
    }


    @Test
    fun testFlowContextCancellation() = runTest {
        val latch = Channel<Unit>()
        val flow = flow {
            assertEquals("delayed", NamedDispatchers.name())
            expect(2)
            emit(1)
        }.flowWith(NamedDispatchers("outer")) {
            map { expect(3); it + 1 }.flowOn(NamedDispatchers("inner"))
        }.map {
            expect(4)
            assertEquals("delayed", NamedDispatchers.name())
            latch.send(Unit)
            hang { expect(6) }
        }.flowOn(NamedDispatchers("delayed"))


        val job = launch(NamedDispatchers("launch")) {
            expect(1)
            flow.single()
        }

        latch.receive()
        expect(5)
        job.cancelAndJoin()
        finish(7)
        ensureActive()
    }

    @Test
    fun testIllegalArgumentException() {
        val flow = emptyFlow<Int>()
        assertFailsWith<IllegalArgumentException> { flow.flowOn(Job()) }
        assertFailsWith<IllegalArgumentException> { flow.flowWith(Job()) { this } }
        assertFailsWith<IllegalArgumentException> { flow.flowOn(EmptyCoroutineContext, bufferSize = -1) }
        assertFailsWith<IllegalArgumentException> { flow.flowWith(EmptyCoroutineContext, bufferSize = -1) { this } }

    }
}
