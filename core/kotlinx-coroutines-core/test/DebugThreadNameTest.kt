/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental

import kotlin.coroutines.experimental.*
import kotlin.test.*

class DebugThreadNameTest : TestBase() {
    @BeforeTest
    fun resetName() {
        resetCoroutineId()
    }

    @Test
    fun testLaunchId() = runTest {
        assertName("coroutine#1")
        launch(coroutineContext) {
            assertName("coroutine#2")
            yield()
            assertName("coroutine#2")
        }
        assertName("coroutine#1")
    }

    @Test
    fun testLaunchIdUndispatched() = runTest {
        assertName("coroutine#1")
        launch(coroutineContext, start = CoroutineStart.UNDISPATCHED) {
            assertName("coroutine#2")
            yield()
            assertName("coroutine#2")
        }
        assertName("coroutine#1")
    }

    @Test
    fun testLaunchName() = runTest {
        assertName("coroutine#1")
        launch(coroutineContext + CoroutineName("TEST")) {
            assertName("TEST#2")
            yield()
            assertName("TEST#2")
        }
        assertName("coroutine#1")
    }

    @Test
    fun testWithContext() = runTest {
        assertName("coroutine#1")
        withContext(DefaultDispatcher) {
            assertName("coroutine#1")
            yield()
            assertName("coroutine#1")
            withContext(CoroutineName("TEST")) {
                assertName("TEST#1")
                yield()
                assertName("TEST#1")
            }
            assertName("coroutine#1")
            yield()
            assertName("coroutine#1")
        }
        assertName("coroutine#1")
    }

    private fun assertName(expected: String) {
        val name = Thread.currentThread().name
        val split = name.split(Regex(" @"))
        assertEquals(2, split.size, "Thread name '$name' is expected to contain one coroutine name")
        assertEquals(expected, split[1], "Thread name '$name' is expected to end with coroutine name '$expected'")
    }
}