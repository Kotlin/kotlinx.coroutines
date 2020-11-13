/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package junit5

import org.assertj.core.api.*
import org.junit.*
import org.junit.platform.engine.discovery.DiscoverySelectors.*
import org.junit.platform.testkit.engine.*
import org.junit.platform.testkit.engine.EventConditions.*
import org.junit.platform.testkit.engine.TestExecutionResultConditions.*
import org.junit.runners.model.*

class CoroutinesTimeoutTest {

    // note that this test is run using JUnit4 in order not to mix the testing systems.
    @Test
    fun testCoroutinesTimeout() {
        EngineTestKit.engine("junit-jupiter")
            .selectors(selectClass(CoroutinesTimeoutSimpleTest::class.java))
            .execute()
            .testEvents()
            .assertThatEvents()
            .testFinishedSuccessfully("ignoresClassTimeout")
            .testFinishedSuccessfully("fitsInClassTimeout")
            .testTimedOut("usesClassTimeout1", 100)
            .testTimedOut("usesClassTimeout2", 100)
            .testTimedOut("usesMethodTimeout", 200)
    }
}

private fun ListAssert<Event>.testFinishedSuccessfully(testName: String): ListAssert<Event> =
    haveExactly(1, event(
        test(testName),
        finishedSuccessfully()
    ))

private fun ListAssert<Event>.testTimedOut(testName: String, after: Int): ListAssert<Event> =
    haveExactly(1, event(
        test(testName),
        finishedWithFailure(instanceOf(TestTimedOutException::class.java), message {
            it.contains(Regex("\\b$after\\b"))
        })
    ))
