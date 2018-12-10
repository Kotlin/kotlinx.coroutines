/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package ordered.tests

import kotlinx.coroutines.*
import kotlinx.coroutines.test.*
import org.junit.*
import org.junit.Test
import java.lang.IllegalStateException
import kotlin.test.*

open class FirstMockedMainTest : TestBase() {

    @Before
    fun setUp() {
        Dispatchers.setMain()
    }

    @After
    fun tearDown() {
        Dispatchers.resetMain()
    }

    @Test
    fun testComponent() {
        val component = TestComponent()
        component.doSomething()
        assertEquals(1, component.launchCompleted)
    }

    @Test
    fun testFailureWhenReset() {
        Dispatchers.resetMain()
        val component = TestComponent()
        try {
            component.doSomething()
            expectUnreached()
        } catch (e: IllegalStateException) {
            assertTrue(e.message!!.contains("Dispatchers.setMain from kotlinx-coroutines-test"))
        }
    }
}
