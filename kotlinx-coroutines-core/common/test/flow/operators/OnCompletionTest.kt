/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlin.test.*

class OnCompletionTest : TestBase() {

    @Test
    fun testOnCompletion() = runTest {
        flow {
            expect(1)
            emit(2)
            expect(4)
        }.onEach {
            expect(2)
        }.onCompletion {
            assertNull(it)
            expect(5)
        }.onEach {
            expect(3)
        }.collect()
        finish(6)
    }

    @Test
    fun testOnCompletionWithException() = runTest {
        flowOf(1).onEach {
            expect(1)
            throw TestException()
        }.onCompletion {
            assertTrue(it is TestException)
            expect(2)
        }.catch {
            assertTrue(it is TestException)
            expect(3)
        }.collect()
        finish(4)
    }

    @Test
    fun testOnCompletionWithExceptionDownstream() = runTest {
        flow {
            expect(1)
            emit(2)
        }.onEach {
            expect(2)
        }.onCompletion {
            assertNull(it)
            expect(4)
        }.onEach {
            expect(3)
            throw TestException()
        }.catch {
            assertTrue(it is TestException)
            expect(5)
        }.collect()
        finish(6)
    }

    @Test
    fun testMultipleOnCompletions() = runTest {
        flowOf(1).onCompletion {
            assertNull(it)
            expect(2)
        }.onEach {
            expect(1)
            throw TestException()
        }.onCompletion {
            assertTrue(it is TestException)
            expect(3)
        }.catch {
            assertTrue(it is TestException)
            expect(4)
        }.collect()
        finish(5)
    }

    @Test
    fun testExceptionFromOnCompletion() = runTest {
        flowOf(1).onEach {
            expect(1)
            throw TestException()
        }.onCompletion {
            expect(2)
            throw TestException2()
        }.catch {
            assertTrue(it is TestException2)
            expect(3)
        }.collect()
        finish(4)
    }

    @Test
    fun testContextPreservation() = runTest {
        flowOf(1).onCompletion {
            assertEquals("OK", NamedDispatchers.name())
            assertNull(it)
            expect(1)
        }.flowOn(NamedDispatchers("OK"))
            .onEach {
                expect(2)
                assertEquals("default", NamedDispatchers.nameOr("default"))
                throw TestException()
            }
            .catch {
                assertTrue(it is TestException)
                expect(3)
            }.collect()
        finish(4)
    }
}
