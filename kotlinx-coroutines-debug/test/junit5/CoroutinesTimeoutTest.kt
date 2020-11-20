/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package junit5

import kotlinx.coroutines.debug.junit5.*
import org.assertj.core.api.*
import org.junit.Ignore
import org.junit.Assert.*
import org.junit.Test
import org.junit.platform.engine.*
import org.junit.platform.engine.discovery.DiscoverySelectors.*
import org.junit.platform.testkit.engine.*
import org.junit.platform.testkit.engine.EventConditions.*
import java.io.*

// note that these tests are run using JUnit4 in order not to mix the testing systems.
class CoroutinesTimeoutTest {

    @Test
    fun testCoroutinesTimeoutSimple() {
        val capturedOut = ByteArrayOutputStream()
        eventsForSelector(selectClass(CoroutinesTimeoutSimpleTest::class.java), capturedOut)
            .testFinishedSuccessfully("ignoresClassTimeout")
            .testFinishedSuccessfully("fitsInClassTimeout")
            .testTimedOut("usesClassTimeout1", 100)
            .testTimedOut("usesMethodTimeout", 200)
            .testTimedOut("usesClassTimeout2", 100)
        assertEquals(capturedOut.toString(), 3, countDumps(capturedOut))
    }

    @Test
    fun testCoroutinesTimeoutMethod() {
        val capturedOut = ByteArrayOutputStream()
        eventsForSelector(selectClass(CoroutinesTimeoutMethodTest::class.java), capturedOut)
            .testFinishedSuccessfully("fitsInMethodTimeout")
            .testFinishedSuccessfully("noClassTimeout")
            .testTimedOut("usesMethodTimeoutWithNoClassTimeout", 100)
        assertEquals(capturedOut.toString(), 1, countDumps(capturedOut))
    }

    @Test
    fun testCoroutinesTimeoutNested() {
        val capturedOut = ByteArrayOutputStream()
        eventsForSelector(selectClass(CoroutinesTimeoutNestedTest::class.java), capturedOut)
            .testFinishedSuccessfully("fitsInOuterClassTimeout")
            .testTimedOut("usesOuterClassTimeout", 200)
        assertEquals(capturedOut.toString(), 1, countDumps(capturedOut))
    }

    @Test
    fun testCoroutinesTimeoutInheritanceWithNoTimeoutInDerived() {
        val capturedOut = ByteArrayOutputStream()
        eventsForSelector(selectClass(CoroutinesTimeoutInheritanceTest.InheritedWithNoTimeout::class.java), capturedOut)
            .testFinishedSuccessfully("methodOverridesBaseClassTimeoutWithGreaterTimeout")
            .testTimedOut("usesBaseClassTimeout", 100)
            .testTimedOut("methodOverridesBaseClassTimeoutWithLesserTimeout", 10)
        assertEquals(capturedOut.toString(), 2, countDumps(capturedOut))
    }

    @Test
    fun testCoroutinesTimeoutInheritanceWithGreaterTimeoutInDerived() {
        val capturedOut = ByteArrayOutputStream()
        eventsForSelector(
            selectClass(CoroutinesTimeoutInheritanceTest.InheritedWithGreaterTimeout::class.java),
            capturedOut
        )
            .testFinishedSuccessfully("classOverridesBaseClassTimeout1")
            .testTimedOut("classOverridesBaseClassTimeout2", 300)
        assertEquals(capturedOut.toString(), 1, countDumps(capturedOut))
    }

    /* Currently there's no ability to replicate [TestFailureValidation] as is for JUnit5:
    https://github.com/junit-team/junit5/issues/506. So, the test mechanism is more ad-hoc. */

    /**
     * This test is disabled due to a race condition between JUnit4 executors that run the given tests
     * in parallel. This led to [DebugProbes.enableCreationStackTraces] being changed while this test is running.
     * Because of this, there is no way for this test to consistently pass when there is more than one executor.
     *
     * In JUnit5, this is less of a problem since tests can be marked with [ResourceLock] to denote that they should not
     * be run in parallel, so this issue is not reason enough to forbid configuring whether to enable the coroutine
     * creation stacktraces. Yet this is enough of a problem to prevent normal testing of the extension in JUnit4.
     *
     * Making all the tests run sequentially (for example, by putting all their code into a single tests) works to show
     * that the issue is solely due to parallelism.
     */
    @Ignore
    @Test
    fun testCoroutinesTimeoutExtensionDisabledTraces() {
        val capturedOut = ByteArrayOutputStream()
        eventsForSelector(selectClass(CoroutinesTimeoutExtensionTest.DisabledStackTracesTest::class.java), capturedOut)
            .testTimedOut("hangingTest", 500)
        assertEquals(false, capturedOut.toString().contains("Coroutine creation stacktrace"))
        assertEquals(capturedOut.toString(), 1, countDumps(capturedOut))
    }

    @Test
    fun testCoroutinesTimeoutExtensionEager() {
        val capturedOut = ByteArrayOutputStream()
        eventsForSelector(selectClass(CoroutinesTimeoutExtensionTest.EagerTest::class.java), capturedOut)
            .testTimedOut("hangingTest", 500)
        for (expectedPart in listOf("hangForever", "waitForHangJob", "BlockingCoroutine{Active}")) {
            assertEquals(expectedPart, true, capturedOut.toString().contains(expectedPart))
        }
        assertEquals(capturedOut.toString(), 1, countDumps(capturedOut))
    }

    @Test
    fun testCoroutinesTimeoutExtensionSimple() {
        val capturedOut = ByteArrayOutputStream()
        eventsForSelector(selectClass(CoroutinesTimeoutExtensionTest.SimpleTest::class.java), capturedOut)
            .testFinishedSuccessfully("successfulTest")
            .testTimedOut("hangingTest", 1000)
            .haveExactly(1, event(
                test("throwingTest"),
                finishedWithFailure(Condition({ it is RuntimeException}, "is RuntimeException"))
            ))
        for (expectedPart in listOf("suspendForever", "invokeSuspend", "BlockingCoroutine{Active}")) {
            assertEquals(expectedPart, true, capturedOut.toString().contains(expectedPart))
        }
        for (nonExpectedPart in listOf("delay", "throwingTest")) {
            assertEquals(nonExpectedPart, false, capturedOut.toString().contains(nonExpectedPart))
        }
        assertEquals(capturedOut.toString(), 1, countDumps(capturedOut))
    }
}

private fun eventsForSelector(selector: DiscoverySelector, capturedOut: OutputStream): ListAssert<Event> {
    val systemOut: PrintStream = System.out
    val systemErr: PrintStream = System.err
    return try {
        System.setOut(PrintStream(capturedOut))
        System.setErr(PrintStream(capturedOut))
        EngineTestKit.engine("junit-jupiter")
            .selectors(selector)
            .execute()
            .testEvents()
            .assertThatEvents()
    } finally {
        System.setOut(systemOut)
        System.setErr(systemErr)
    }
}

private fun ListAssert<Event>.testFinishedSuccessfully(testName: String): ListAssert<Event> =
    haveExactly(1, event(
        test(testName),
        finishedSuccessfully()
    ))

private fun ListAssert<Event>.testTimedOut(testName: String, after: Long): ListAssert<Event> =
    haveExactly(1, event(
        test(testName),
        finishedWithFailure(Condition({ it is CoroutinesTimeoutException && it.timeoutMs == after },
            "is CoroutinesTimeoutException($after)"))
    ))

/** Counts the number of occurrences of "Coroutines dump" in [capturedOut] */
private fun countDumps(capturedOut: ByteArrayOutputStream): Int {
    var result = 0
    val outStr = capturedOut.toString()
    val header = "Coroutines dump"
    var i = 0
    while (i < outStr.length - header.length) {
        if (outStr.substring(i, i + header.length) == header) {
            result += 1
            i += header.length
        } else {
            i += 1
        }
    }
    return result
}