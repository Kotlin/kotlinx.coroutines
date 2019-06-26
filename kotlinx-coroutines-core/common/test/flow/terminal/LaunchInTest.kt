/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlin.test.*

class LaunchInTest : TestBase() {

    @Test
    fun testLaunchIn() = runTest {
        val flow = flow {
            expect(1)
            emit(1)
            throw TestException()
        }.onEach {
            assertEquals(1, it)
            expect(2)
        }.onCompletion {
            assertTrue(it is TestException)
            expect(3)
        }.catch {
            assertTrue { it is TestException }
            expect(4)
        }

        flow.launchIn(this).join()
        finish(5)
    }

    @Test
    fun testDispatcher() = runTest {
        flow {
            assertEquals("flow", NamedDispatchers.name())
            emit(1)
            expect(1)
        }.launchIn(this + NamedDispatchers("flow")).join()
        finish(2)
    }

    @Test
    fun testUnhandledError() = runTest(expected = { it is TestException }) {
        flow {
            emit(1)
            expect(1)
        }.catch {
            expectUnreached()
        }.onCompletion {
            finish(2)
            throw TestException()
        }.launchIn(this)
    }

}
