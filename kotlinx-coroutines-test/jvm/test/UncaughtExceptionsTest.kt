package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlinx.coroutines.testing.*
import org.junit.Test
import kotlin.test.*

/**
 * Tests that check the behavior of the test framework when there are stray uncaught exceptions.
 * These tests are JVM-only because only the JVM allows to set a global uncaught exception handler and validate the
 * behavior without checking the test logs.
 * Nevertheless, each test here has a corresponding test in the common source set that can be run manually.
 */
class UncaughtExceptionsTest {

    val oldExceptionHandler = Thread.getDefaultUncaughtExceptionHandler()
    val uncaughtExceptions = mutableListOf<Throwable>()

    @BeforeTest
    fun setUp() {
        Thread.setDefaultUncaughtExceptionHandler { thread, throwable ->
            uncaughtExceptions.add(throwable)
        }
    }

    @AfterTest
    fun tearDown() {
        Thread.setDefaultUncaughtExceptionHandler(oldExceptionHandler)
    }

    @Test
    fun testReportingStrayUncaughtExceptionsBetweenTests() {
        TestScopeTest().testReportingStrayUncaughtExceptionsBetweenTests()
        assertEquals(1, uncaughtExceptions.size, "Expected 1 uncaught exception, but got $uncaughtExceptions")
        val exception = assertIs<TestException>(uncaughtExceptions.single())
        assertEquals("x", exception.message)
    }

    @Test
    fun testExceptionCaptorCleanedUpOnPreliminaryExit() {
        RunTestTest().testExceptionCaptorCleanedUpOnPreliminaryExit()
        assertEquals(2, uncaughtExceptions.size, "Expected 2 uncaught exceptions, but got $uncaughtExceptions")
        for (exception in uncaughtExceptions) {
            assertIs<TestException>(exception)
        }
        assertEquals("A", uncaughtExceptions[0].message)
        assertEquals("B", uncaughtExceptions[1].message)
    }
}
