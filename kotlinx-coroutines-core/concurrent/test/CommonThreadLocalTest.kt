/*
 * Copyright 2016-2022 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.exceptions.*
import kotlinx.coroutines.internal.*
import kotlin.test.*

class CommonThreadLocalTest: TestBase() {

    /**
     * Tests the basic functionality of [commonThreadLocal]: storing a separate value for each thread.
     */
    @Test
    fun testThreadLocalBeingThreadLocal() = runTest {
        val threadLocal = commonThreadLocal<Int>(Symbol("Test1"))
        newSingleThreadContext("").use {
            threadLocal.set(10)
            assertEquals(10, threadLocal.get())
            val job1 = launch(it) {
                threadLocal.set(20)
                assertEquals(20, threadLocal.get())
            }
            assertEquals(10, threadLocal.get())
            job1.join()
            val job2 = launch(it) {
                assertEquals(20, threadLocal.get())
            }
            job2.join()
        }
    }

    /**
     * Tests using [commonThreadLocal] with a nullable type.
     */
    @Test
    fun testThreadLocalWithNullableType() = runTest {
        val threadLocal = commonThreadLocal<Int?>(Symbol("Test2"))
        newSingleThreadContext("").use {
            assertNull(threadLocal.get())
            threadLocal.set(10)
            assertEquals(10, threadLocal.get())
            val job1 = launch(it) {
                assertNull(threadLocal.get())
                threadLocal.set(20)
                assertEquals(20, threadLocal.get())
            }
            assertEquals(10, threadLocal.get())
            job1.join()
            threadLocal.set(null)
            assertNull(threadLocal.get())
            val job2 = launch(it) {
                assertEquals(20, threadLocal.get())
                threadLocal.set(null)
                assertNull(threadLocal.get())
            }
            job2.join()
        }
    }

    /**
     * Tests that several instances of [commonThreadLocal] with different names don't affect each other.
     */
    @Test
    fun testThreadLocalsWithDifferentNamesNotInterfering() {
        val value1 = commonThreadLocal<Int>(Symbol("Test3a"))
        val value2 = commonThreadLocal<Int>(Symbol("Test3b"))
        value1.set(5)
        value2.set(6)
        assertEquals(5, value1.get())
        assertEquals(6, value2.get())
    }
}
