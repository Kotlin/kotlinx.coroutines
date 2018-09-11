/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.slf4j

import kotlinx.coroutines.experimental.*
import org.junit.*
import org.junit.Test
import org.slf4j.*
import kotlin.coroutines.experimental.*
import kotlin.test.*

class MDCContextTest : TestBase() {
    @Before
    fun setUp() {
        MDC.clear()
    }

    @After
    fun tearDown() {
        MDC.clear()
    }

    @Test
    fun testContextIsNotPassedByDefaultBetweenCoroutines() = runTest {
        expect(1)
        MDC.put("myKey", "myValue")
        // Standalone launch
        GlobalScope.launch {
            assertEquals(null, MDC.get("myKey"))
            expect(2)
        }.join()
        finish(3)
    }

    @Test
    fun testContextCanBePassedBetweenCoroutines() = runTest {
        expect(1)
        MDC.put("myKey", "myValue")
        // Scoped launch with MDCContext element
        launch(MDCContext()) {
            assertEquals("myValue", MDC.get("myKey"))
            expect(2)
        }.join()

        finish(3)
    }

    @Test
    fun testContextInheritance() = runTest {
        expect(1)
        MDC.put("myKey", "myValue")
        withContext(MDCContext()) {
            MDC.put("myKey", "myValue2")
            // Scoped launch with inherited MDContext element
            launch(Dispatchers.Default) {
                assertEquals("myValue", MDC.get("myKey"))
                expect(2)
            }.join()

            finish(3)
        }
        assertEquals("myValue", MDC.get("myKey"))
    }

    @Test
    fun testContextPassedWhileOnMainThread() {
        MDC.put("myKey", "myValue")
        // No MDCContext element
        runBlocking {
            assertEquals("myValue", MDC.get("myKey"))
        }
    }

    @Test
    fun testContextCanBePassedWhileOnMainThread() {
        MDC.put("myKey", "myValue")
        runBlocking(MDCContext()) {
            assertEquals("myValue", MDC.get("myKey"))
        }
    }

    @Test
    fun testContextNeededWithOtherContext() {
        MDC.put("myKey", "myValue")
        runBlocking(MDCContext()) {
            assertEquals("myValue", MDC.get("myKey"))
        }
    }

    @Test
    fun testContextMayBeEmpty() {
        runBlocking(MDCContext()) {
            assertEquals(null, MDC.get("myKey"))
        }
    }

    @Test
    fun testContextWithContext() = runTest {
        MDC.put("myKey", "myValue")
        val mainDispatcher = kotlin.coroutines.experimental.coroutineContext[ContinuationInterceptor]!!
        withContext(Dispatchers.Default + MDCContext()) {
            assertEquals("myValue", MDC.get("myKey"))
            withContext(mainDispatcher) {
                assertEquals("myValue", MDC.get("myKey"))
            }
        }
    }
}