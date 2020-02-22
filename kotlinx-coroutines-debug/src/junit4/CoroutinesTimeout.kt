/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.debug.junit4

import kotlinx.coroutines.debug.*
import org.junit.rules.*
import org.junit.runner.*
import org.junit.runners.model.*
import java.util.concurrent.*

/**
 * Coroutines timeout rule for JUnit4 that is applied to all methods in the class.
 * This rule is very similar to [Timeout] rule: it runs tests in a separate thread,
 * fails tests after the given timeout and interrupts test thread.
 *
 * Additionally, this rule installs [DebugProbes] and dumps all coroutines at the moment of the timeout.
 * It may cancel coroutines on timeout if [cancelOnTimeout] set to `true`.
 *
 * Example of usage:
 * ```
 * class HangingTest {
 *     @get:Rule
 *     val timeout = CoroutinesTimeout.seconds(5)
 *
 *     @Test
 *     fun testThatHangs() = runBlocking {
 *          ...
 *          delay(Long.MAX_VALUE) // somewhere deep in the stack
 *          ...
 *     }
 * }
 * ```
 */
public class CoroutinesTimeout(
    private val testTimeoutMs: Long,
    private val cancelOnTimeout: Boolean = false
) : TestRule {

    init {
        require(testTimeoutMs > 0) { "Expected positive test timeout, but had $testTimeoutMs" }
        /*
         * Install probes in the constructor, so all the coroutines launched from within
         * target test constructor will be captured
         */
        DebugProbes.install()
    }

    companion object {
        /**
         * Creates [CoroutinesTimeout] rule with the given timeout in seconds.
         */
        public fun seconds(seconds: Int, cancelOnTimeout: Boolean = false): CoroutinesTimeout =
            seconds(seconds.toLong(), cancelOnTimeout)

        /**
         * Creates [CoroutinesTimeout] rule with the given timeout in seconds.
         */
        public fun seconds(seconds: Long, cancelOnTimeout: Boolean = false): CoroutinesTimeout =
            CoroutinesTimeout(TimeUnit.SECONDS.toMillis(seconds), cancelOnTimeout) // Overflow is properly handled by TimeUnit
    }

    /**
     * @suppress suppress from Dokka
     */
    override fun apply(base: Statement, description: Description): Statement =
        CoroutinesTimeoutStatement(base, description, testTimeoutMs, cancelOnTimeout)
}
