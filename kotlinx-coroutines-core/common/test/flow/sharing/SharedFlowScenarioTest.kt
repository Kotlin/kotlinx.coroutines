/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlin.coroutines.*
import kotlin.test.*

/**
 * This test suit for [SharedFlow] has a dense framework that allows to test complex
 * suspend/resume scenarios while keeping the code readable. Each test here is for
 * one specific [SharedFlow] configuration, testing all the various corner cases in its
 * behavior.
 */
class SharedFlowScenarioTest : TestBase() {
    @Test
    fun testReplay1Extra2() =
        testSharedFlow(MutableSharedFlow<Int>(1, 2)) {
            // total buffer size == 3
            expectReplayOf()
            emitRightNow(1); expectReplayOf(1)
            emitRightNow(2); expectReplayOf(2)
            emitRightNow(3); expectReplayOf(3)
            emitRightNow(4); expectReplayOf(4) // no prob - no subscribers
            val a = subscribe("a"); collect(a, 4)
            emitRightNow(5); expectReplayOf(5)
            emitRightNow(6); expectReplayOf(6)
            emitRightNow(7); expectReplayOf(7)
            // suspend/collect sequentially
            val e8 = emitSuspends(8); collect(a, 5); emitResumes(e8); expectReplayOf(8)
            val e9 = emitSuspends(9); collect(a, 6); emitResumes(e9); expectReplayOf(9)
            // buffer full, but parallel emitters can still suspend (queue up)
            val e10 = emitSuspends(10)
            val e11 = emitSuspends(11)
            val e12 = emitSuspends(12)
            collect(a, 7); emitResumes(e10); expectReplayOf(10) // buffer 8, 9 | 10
            collect(a, 8); emitResumes(e11); expectReplayOf(11) // buffer 9, 10 | 11
            sharedFlow.resetReplayCache(); expectReplayOf() // 9, 10 11 | no replay
            collect(a, 9); emitResumes(e12); expectReplayOf(12)
            collect(a, 10, 11, 12); expectReplayOf(12) // buffer empty | 12
            emitRightNow(13); expectReplayOf(13)
            emitRightNow(14); expectReplayOf(14)
            emitRightNow(15); expectReplayOf(15) // buffer 13, 14 | 15
            val e16 = emitSuspends(16)
            val e17 = emitSuspends(17)
            val e18 = emitSuspends(18)
            cancel(e17); expectReplayOf(15) // cancel in the middle of three emits; buffer 13, 14 | 15
            collect(a, 13); emitResumes(e16); expectReplayOf(16) // buffer 14, 15, | 16
            collect(a, 14); emitResumes(e18); expectReplayOf(18) // buffer 15, 16 | 18
            val e19 = emitSuspends(19)
            val e20 = emitSuspends(20)
            val e21 = emitSuspends(21)
            cancel(e21); expectReplayOf(18) // cancel last emit; buffer 15, 16, 18
            collect(a, 15); emitResumes(e19); expectReplayOf(19) // buffer 16, 18 | 19
            collect(a, 16); emitResumes(e20); expectReplayOf(20) // buffer 18, 19 | 20
            collect(a, 18, 19, 20); expectReplayOf(20) // buffer empty | 20
            emitRightNow(22); expectReplayOf(22)
            emitRightNow(23); expectReplayOf(23)
            emitRightNow(24); expectReplayOf(24) // buffer 22, 23 | 24
            val e25 = emitSuspends(25)
            val e26 = emitSuspends(26)
            val e27 = emitSuspends(27)
            cancel(e25); expectReplayOf(24) // cancel first emit, buffer 22, 23 | 24
            sharedFlow.resetReplayCache(); expectReplayOf() // buffer 22, 23, 24 | no replay
            val b = subscribe("b") // new subscriber
            collect(a, 22); emitResumes(e26); expectReplayOf(26) // buffer 23, 24 | 26
            collect(b, 26)
            collect(a, 23); emitResumes(e27); expectReplayOf(27) // buffer 24, 26 | 27
            collect(a, 24, 26, 27) // buffer empty | 27
            emitRightNow(28); expectReplayOf(28)
            emitRightNow(29); expectReplayOf(29) // buffer 27, 28 | 29
            collect(a, 28, 29) // but b is slow
            val e30 = emitSuspends(30)
            val e31 = emitSuspends(31)
            val e32 = emitSuspends(32)
            val e33 = emitSuspends(33)
            val e34 = emitSuspends(34)
            val e35 = emitSuspends(35)
            val e36 = emitSuspends(36)
            val e37 = emitSuspends(37)
            val e38 = emitSuspends(38)
            val e39 = emitSuspends(39)
            cancel(e31) // cancel emitter in queue
            cancel(b) // cancel slow subscriber -> 3 emitters resume
            emitResumes(e30); emitResumes(e32); emitResumes(e33); expectReplayOf(33) // buffer 30, 32 | 33
            val c = subscribe("c"); collect(c, 33) // replays
            cancel(e34)
            collect(a, 30); emitResumes(e35); expectReplayOf(35) // buffer 32, 33 | 35
            cancel(e37)
            cancel(a); emitResumes(e36); emitResumes(e38); expectReplayOf(38) // buffer 35, 36 | 38
            collect(c, 35); emitResumes(e39); expectReplayOf(39) // buffer 36, 38 | 39
            collect(c, 36, 38, 39); expectReplayOf(39)
            cancel(c); expectReplayOf(39) // replay stays
        }

    @Test
    fun testReplay1() =
        testSharedFlow(MutableSharedFlow<Int>(1)) {
            emitRightNow(0); expectReplayOf(0)
            emitRightNow(1); expectReplayOf(1)
            emitRightNow(2); expectReplayOf(2)
            sharedFlow.resetReplayCache(); expectReplayOf()
            sharedFlow.resetReplayCache(); expectReplayOf()
            emitRightNow(3); expectReplayOf(3)
            emitRightNow(4); expectReplayOf(4)
            val a = subscribe("a"); collect(a, 4)
            emitRightNow(5); expectReplayOf(5); collect(a, 5)
            emitRightNow(6)
            sharedFlow.resetReplayCache(); expectReplayOf()
            sharedFlow.resetReplayCache(); expectReplayOf()
            val e7 = emitSuspends(7)
            val e8 = emitSuspends(8)
            val e9 = emitSuspends(9)
            collect(a, 6); emitResumes(e7); expectReplayOf(7)
            sharedFlow.resetReplayCache(); expectReplayOf()
            sharedFlow.resetReplayCache(); expectReplayOf() // buffer 7 | -- no replay, but still buffered
            val b = subscribe("b")
            collect(a, 7); emitResumes(e8); expectReplayOf(8)
            collect(b, 8) // buffer | 8 -- a is slow
            val e10 = emitSuspends(10)
            val e11 = emitSuspends(11)
            val e12 = emitSuspends(12)
            cancel(e9)
            collect(a, 8); emitResumes(e10); expectReplayOf(10)
            collect(a, 10) // now b's slow
            cancel(e11)
            collect(b, 10); emitResumes(e12); expectReplayOf(12)
            collect(a, 12)
            collect(b, 12)
            sharedFlow.resetReplayCache(); expectReplayOf()
            sharedFlow.resetReplayCache(); expectReplayOf() // nothing is buffered -- both collectors up to date
            emitRightNow(13); expectReplayOf(13)
            collect(b, 13) // a is slow
            val e14 = emitSuspends(14)
            val e15 = emitSuspends(15)
            val e16 = emitSuspends(16)
            cancel(e14)
            cancel(a); emitResumes(e15); expectReplayOf(15) // cancelling slow subscriber
            collect(b, 15); emitResumes(e16); expectReplayOf(16)
            collect(b, 16)
        }

    @Test
    fun testReplay2Extra2DropOldest() =
        testSharedFlow<Int>(MutableSharedFlow(2, 2, BufferOverflow.DROP_OLDEST)) {
            emitRightNow(0); expectReplayOf(0)
            emitRightNow(1); expectReplayOf(0, 1)
            emitRightNow(2); expectReplayOf(1, 2)
            emitRightNow(3); expectReplayOf(2, 3)
            emitRightNow(4); expectReplayOf(3, 4)
            val a = subscribe("a")
            collect(a, 3)
            emitRightNow(5); expectReplayOf(4, 5)
            emitRightNow(6); expectReplayOf(5, 6)
            emitRightNow(7); expectReplayOf(6, 7) // buffer 4, 5 | 6, 7
            emitRightNow(8); expectReplayOf(7, 8) // buffer 5, 6 | 7, 8
            emitRightNow(9); expectReplayOf(8, 9) // buffer 6, 7 | 8, 9
            collect(a, 6, 7)
            val b = subscribe("b")
            collect(b, 8, 9) // buffer | 8, 9
            emitRightNow(10); expectReplayOf(9, 10) // buffer 8 | 9, 10
            collect(a, 8, 9, 10) // buffer | 9, 10, note "b" had not collected 10 yet
            emitRightNow(11); expectReplayOf(10, 11) // buffer | 10, 11
            emitRightNow(12); expectReplayOf(11, 12) // buffer 10 | 11, 12
            emitRightNow(13); expectReplayOf(12, 13) // buffer 10, 11 | 12, 13
            emitRightNow(14); expectReplayOf(13, 14) // buffer 11, 12 | 13, 14, "b" missed 10
            collect(b, 11, 12, 13, 14)
            sharedFlow.resetReplayCache(); expectReplayOf() // buffer 11, 12, 13, 14 |
            sharedFlow.resetReplayCache(); expectReplayOf()
            collect(a, 11, 12, 13, 14)
            emitRightNow(15); expectReplayOf(15)
            collect(a, 15)
            collect(b, 15)
        }

    private fun <T> testSharedFlow(
        sharedFlow: MutableSharedFlow<T>,
        scenario: suspend ScenarioDsl<T>.() -> Unit
    ) = runTest {
        var dsl: ScenarioDsl<T>? = null
        try {
            coroutineScope {
                dsl = ScenarioDsl<T>(sharedFlow, coroutineContext)
                dsl!!.scenario()
                dsl!!.stop()
            }
        } catch (e: Throwable) {
            dsl?.printLog()
            throw e
        }
    }

    private data class TestJob(val job: Job, val name: String) {
        override fun toString(): String = name
    }

    private open class Action
    private data class EmitResumes(val job: TestJob) : Action()
    private data class Collected(val job: TestJob, val value: Any?) : Action()
    private data class ResumeCollecting(val job: TestJob) : Action()
    private data class Cancelled(val job: TestJob) : Action()

    @OptIn(ExperimentalStdlibApi::class)
    private class ScenarioDsl<T>(
        val sharedFlow: MutableSharedFlow<T>,
        coroutineContext: CoroutineContext
    ) {
        private val log = ArrayList<String>()
        private val timeout = 10000L
        private val scope = CoroutineScope(coroutineContext + Job())
        private val actions = HashSet<Action>()
        private val actionWaiters = ArrayDeque<Continuation<Unit>>()
        private var expectedReplay = emptyList<T>()

        private fun checkReplay() {
            assertEquals(expectedReplay, sharedFlow.replayCache)
        }

        private fun wakeupWaiters() {
            repeat(actionWaiters.size) {
                actionWaiters.removeFirst().resume(Unit)
            }
        }

        private fun addAction(action: Action) {
            actions.add(action)
            wakeupWaiters()
        }

        private suspend fun awaitAction(action: Action) {
            withTimeoutOrNull(timeout) {
                while (!actions.remove(action)) {
                    suspendCancellableCoroutine<Unit> { actionWaiters.add(it) }
                }
            } ?: error("Timed out waiting for action: $action")
            wakeupWaiters()
        }

        private fun launchEmit(a: T): TestJob {
            val name = "emit($a)"
            val job = scope.launch(start = CoroutineStart.UNDISPATCHED) {
                val job = TestJob(coroutineContext[Job]!!, name)
                try {
                    log(name)
                    sharedFlow.emit(a)
                    log("$name resumes")
                    addAction(EmitResumes(job))
                } catch(e: CancellationException) {
                    log("$name cancelled")
                    addAction(Cancelled(job))
                }
            }
            return TestJob(job, name)
        }

        fun expectReplayOf(vararg a: T) {
            expectedReplay = a.toList()
            checkReplay()
        }

        fun emitRightNow(a: T) {
            val job = launchEmit(a)
            assertTrue(actions.remove(EmitResumes(job)))
        }

        fun emitSuspends(a: T): TestJob {
            val job = launchEmit(a)
            assertFalse(EmitResumes(job) in actions)
            checkReplay()
            return job
        }

        suspend fun emitResumes(job: TestJob) {
            awaitAction(EmitResumes(job))
        }

        suspend fun cancel(job: TestJob) {
            log("cancel(${job.name})")
            job.job.cancel()
            awaitAction(Cancelled(job))
        }

        fun subscribe(id: String): TestJob {
            val name = "collect($id)"
            val job = scope.launch(start = CoroutineStart.UNDISPATCHED) {
                val job = TestJob(coroutineContext[Job]!!, name)
                try {
                    awaitAction(ResumeCollecting(job))
                    log("$name start")
                    sharedFlow.collect { value ->
                        log("$name -> $value")
                        addAction(Collected(job, value))
                        awaitAction(ResumeCollecting(job))
                        log("$name -> $value resumes")
                    }
                    error("$name completed")
                } catch(e: CancellationException) {
                    log("$name cancelled")
                    addAction(Cancelled(job))
                }
            }
            return TestJob(job, name)
        }

        suspend fun collect(job: TestJob, vararg a: T) {
            for (value in a) {
                checkReplay() // should not have changed
                addAction(ResumeCollecting(job))
                awaitAction(Collected(job, value))
            }
        }

        fun stop() {
            log("--- stop")
            scope.cancel()
        }

        private fun log(text: String) {
            log.add(text)
        }

        fun printLog() {
            println("--- The most recent log entries ---")
            log.takeLast(30).forEach(::println)
            println("--- That's it ---")
        }
    }
}