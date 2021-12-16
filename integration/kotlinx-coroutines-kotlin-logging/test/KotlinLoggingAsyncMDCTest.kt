/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

import kotlinx.coroutines.*
import kotlinx.coroutines.kotlinlogging.*
import org.apache.logging.log4j.*
import org.apache.logging.log4j.core.config.*
import org.junit.*
import org.junit.Test
import org.slf4j.*
import kotlin.test.*

class KotlinLoggingAsyncMDCTest : TestBase() {
    init {
        Configurator.setRootLevel(Level.TRACE)
    }

    @Before
    fun beforeEach() {
        MDC.clear()
    }

    @Test
    fun `simple pair withLoggingContext`() = runTest {
        expect(1)
        assertNull(MDC.get("a"))

        withLoggingContextAsync("a" to "c") {

            expect(2)
            withLoggingContextAsync("a" to "b") {
                assertEquals("b", MDC.get("a"))
                expect(3)
            }

            assertEquals("c", MDC.get("a"))
        }
        assertNull(MDC.get("a"))
        finish(4)
    }

    @Test
    fun `simple pair withLoggingContext (restorePrevious=false)`() = runTest {
        expect(1)
        withLoggingContextAsync("a" to "c") {
            withLoggingContextAsync("a" to "b", restorePrevious = false) {
                expect(2)
                assertEquals("b", MDC.get("a"))
            }
            expect(3)
            assertNull(MDC.get("a"))
        }
        assertNull(MDC.get("a"))
        expect(4)

        withLoggingContextAsync("a" to "c", restorePrevious = false) {
            withLoggingContextAsync("a" to "b") {
                expect(5)
                assertEquals("b", MDC.get("a"))
            }
            expect(6)
            assertEquals("c", MDC.get("a"))
        }
        assertNull(MDC.get("a"))
        finish(7)
    }

    @Test
    fun `simple nullable pair withLoggingContext`() = runTest {
        expect(1)
        assertNull(MDC.get("a"))
        withLoggingContextAsync("a" to null) {
            assertNull(MDC.get("a"))
            expect(2)
        }
        assertNull(MDC.get("a"))

        MDC.put("a", "b")
        assertEquals("b", MDC.get("a"))
        expect(3)
        withLoggingContextAsync("a" to null) {
            assertEquals("b", MDC.get("a"))
            expect(4)
        }
        assertEquals("b", MDC.get("a"))
        finish(5)
    }

    @Test
    fun `multiple pair withLoggingContext`() = runTest {
        expect(1)
        MDC.put("f", "g")

        assertNull(MDC.get("a"))
        assertNull(MDC.get("c"))
        assertNull(MDC.get("e"))
        assertEquals("g", MDC.get("f"))

        withLoggingContextAsync("a" to "h", "c" to "i") {
            expect(2)
            assertEquals("h", MDC.get("a"))
            assertEquals("i", MDC.get("c"))
            assertNull(MDC.get("e"))
            assertEquals("g", MDC.get("f"))

            withLoggingContextAsync("a" to "b", "c" to "d", "e" to null, "f" to null) {
                expect(3)

                assertEquals("b", MDC.get("a"))
                assertEquals("d", MDC.get("c"))
                assertNull(MDC.get("e"))
                assertEquals("g", MDC.get("f"))
            }
            expect(4)
            assertEquals("h", MDC.get("a"))
            assertEquals("i", MDC.get("c"))
            assertNull(MDC.get("e"))
            assertEquals("g", MDC.get("f"))
        }
        expect(5)
        assertNull(MDC.get("a"))
        assertNull(MDC.get("c"))
        assertNull(MDC.get("e"))
        assertEquals("g", MDC.get("f"))
        finish(6)
    }

    @Test
    fun `multiple pair withLoggingContext (restorePrevious=false)`() = runTest {
        expect(1)
        MDC.put("f", "g")

        assertNull(MDC.get("a"))
        assertNull(MDC.get("c"))
        assertNull(MDC.get("e"))
        assertEquals("g", MDC.get("f"))

        withLoggingContextAsync(
            "a" to "b",
            "c" to "d",
            "e" to null,
            "f" to null,
            restorePrevious = false
        ) {
            expect(2)
            assertEquals("b", MDC.get("a"))
            assertEquals("d", MDC.get("c"))
            assertNull(MDC.get("e"))
            assertEquals("g", MDC.get("f"))
        }
        expect(3)
        assertNull(MDC.get("a"))
        assertNull(MDC.get("c"))
        assertNull(MDC.get("e"))
        assertEquals("g", MDC.get("f"))
        finish(4)
    }

    @Test
    fun `map withLoggingContext`() = runTest {
        expect(1)
        assertNull(MDC.get("a"))
        assertNull(MDC.get("c"))
        assertNull(MDC.get("e"))
        assertNull(MDC.get("f"))
        assertNull(MDC.get("k"))

        MDC.put("e", "g")
        MDC.put("k", "l")

        withLoggingContextAsync(mapOf("a" to "b", "c" to "d", "e" to null, "f" to "h")) {
            expect(2)
            assertEquals("b", MDC.get("a"))
            assertEquals("d", MDC.get("c"))
            assertEquals("g", MDC.get("e"))
            assertEquals("h", MDC.get("f"))
            assertEquals("l", MDC.get("k"))

            withLoggingContextAsync(mapOf("a" to "b", "e" to "i", "f" to "j")) {
                expect(3)
                assertEquals("b", MDC.get("a"))
                assertEquals("d", MDC.get("c"))
                assertEquals("i", MDC.get("e"))
                assertEquals("j", MDC.get("f"))
                assertEquals("l", MDC.get("k"))
            }

            expect(4)
            assertEquals("b", MDC.get("a"))
            assertEquals("d", MDC.get("c"))
            assertEquals("g", MDC.get("e"))
            assertEquals("h", MDC.get("f"))
            assertEquals("l", MDC.get("k"))
        }

        expect(5)
        assertNull(MDC.get("a"))
        assertNull(MDC.get("c"))
        assertEquals("g", MDC.get("e"))
        assertNull(MDC.get("f"))
        assertEquals("l", MDC.get("k"))
        finish(6)
    }
}
