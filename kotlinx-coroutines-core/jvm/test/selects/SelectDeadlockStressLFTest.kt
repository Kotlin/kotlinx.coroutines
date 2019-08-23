/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.selects

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import org.junit.*
import kotlin.math.*

/**
 * A stress-test on lock-freedom of select sending/receiving into opposite channels.
 */
class SelectDeadlockStressLFTest : TestBase() {
    private val env = LockFreedomTestEnvironment("SelectDeadlockStressLFTest", allowSuspendedThreads = 1)
    private val nSeconds = 60 * stressTestMultiplier

    private val c1 = Channel<Long>()
    private val c2 = Channel<Long>()

    @Test
    fun testStress() = testScenarios(
//        "s1r2",
//        "s2r1",
//        "s1r2",
//        "s2r1"
        "s1",
        "s2",
        "r1",
        "r2"
    )

    private fun testScenarios(vararg scenarios: String) {
        val t = scenarios.mapIndexed { i, scenario ->
            val idx = i + 1L
            TestDef(idx, "$idx [$scenario]", scenario)
        }
        t.forEach { it.test() }
//        var i = 0
        env.performTest(nSeconds) {
            t.forEach { println(it) }
//            if (i++ == 1) {
//                println("!!!")
//            }
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

        private suspend fun doSendReceive() =
            select<Unit> {
                for (clause in clauses) clause()
            }

        private fun SelectBuilder<Unit>.sendClause(c: Channel<Long>) =
            c.onSend(sendIndex) {
//                    println("$name: Send: $sendIndex")
                sendIndex += 4L
//                    if (sendIndex >= 30) {
//                        println("STOP")
//                    }
            }

        private fun SelectBuilder<Unit>.receiveClause(c: Channel<Long>) =
            c.onReceive { i ->
//                  println("$name: Rcvd: $i")
                receiveIndex = max(i, receiveIndex)
            }

        override fun toString(): String = "$name: send=$sendIndex, received=$receiveIndex"
    }
}