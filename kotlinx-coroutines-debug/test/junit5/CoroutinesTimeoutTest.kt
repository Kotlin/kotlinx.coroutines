/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package junit5

import kotlinx.coroutines.debug.junit5.*
import org.assertj.core.api.*
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
    fun testCoroutinesTimeout() {
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