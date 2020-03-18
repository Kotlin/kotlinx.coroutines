/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.selects

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import org.junit.*
import org.junit.Ignore
import org.junit.Test
import kotlin.math.*
import kotlin.test.*

/**
 * A stress-test on lock-freedom of select sending/receiving into opposite channels.
 */
class SelectDeadlockLFStressTest : TestBase() {
    private val env = LockFreedomTestEnvironment("SelectDeadlockLFStressTest", allowSuspendedThreads = 1)
    private val nSeconds = 5 * stressTestMultiplier

    private val c1 = Channel<Long>()
    private val c2 = Channel<Long>()

    @Test
    fun testLockFreedom() = testScenarios(
        "s1r2",
        "s2r1",
        "r1s2",
        "r2s1"
    )

    private fun testScenarios(vararg scenarios: String) {
        env.onCompletion {
            c1.cancel(TestCompleted())
            c2.cancel(TestCompleted())
        }
        val t = scenarios.mapIndexed { i, scenario ->
            val idx = i + 1L
            TestDef(idx, "$idx [$scenario]", scenario)
        }
        t.forEach { it.test() }
        env.performTest(nSeconds) {
            t.forEach { println(it) }
        }
    }

    private inner class TestDef(
        var sendIndex: Long = 0L,
        val name: String,
        scenario: String
    ) {
        var receiveIndex = 0L

        val clauses: List<SelectBuilder<Unit>.() -> Unit> = ArrayList<SelectBuilder<Unit>.() -> Unit>().apply {
            require(scenario.length % 2 == 0)
            for (i in scenario.indices step 2) {
                val ch = when (val c = scenario[i + 1]) {
                    '1' -> c1
                    '2' -> c2
                    else -> error("Channel '$c'")
                }
                val clause = when (val op = scenario[i]) {
                    's' -> fun SelectBuilder<Unit>.() { sendClause(ch) }
                    'r' -> fun SelectBuilder<Unit>.() { receiveClause(ch) }
                    else -> error("Operation '$op'")
                }
                add(clause)
            }
        }

        fun test() = env.testThread(name) {
            doSendReceive()
        }

        private suspend fun doSendReceive() {
            try {
                select<Unit> {
                    for (clause in clauses) clause()
                }
            } catch (e: TestCompleted) {
                assertTrue(env.isCompleted)
            }
        }

        private fun SelectBuilder<Unit>.sendClause(c: Channel<Long>) =
            c.onSend(sendIndex) {
                sendIndex += 4L
            }

        private fun SelectBuilder<Unit>.receiveClause(c: Channel<Long>) =
            c.onReceive { i ->
                receiveIndex = max(i, receiveIndex)
            }

        override fun toString(): String = "$name: send=$sendIndex, received=$receiveIndex"
    }

    private class TestCompleted : CancellationException()
}