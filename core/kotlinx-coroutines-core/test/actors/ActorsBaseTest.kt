/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.actors

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.channels.*
import org.junit.Test
import org.junit.runner.*
import org.junit.runners.*
import java.io.*
import kotlin.coroutines.experimental.*
import kotlin.test.*

@RunWith(Parameterized::class)
class ActorsBaseTest(private val actorType: ActorType) : TestBase() {

    companion object {
        @Parameterized.Parameters(name = "{0}")
        @JvmStatic
        fun params(): Collection<Array<Any>> =
            ActorType.values().map { arrayOf<Any>(it) }
    }

    enum class ActorType {
        Actor, // lower case for prettier test names
        TypedActor
    }

    private fun TestActor(
        context: CoroutineContext,
        capacity: Int = 2, parent: Job? = null,
        whenClosed: () -> Unit = {},
        whenStarted: () -> Unit = {}
    ): TestActor {
        return when (actorType) {
            ActorType.Actor -> ActTestActor(context.minusKey(Job), capacity, parent, whenClosed, whenStarted)
            ActorType.TypedActor -> TypedTestActor(context.minusKey(Job), capacity, parent, whenClosed, whenStarted)
        }
    }

    // Common interface for tests
    private interface TestActor {
        suspend fun expectedSequence(expected: Int)
        suspend fun fail()

        public fun close()
        public fun cancel()
        public suspend fun join()
    }

    private inner class TypedTestActor(
        context: CoroutineContext,
        capacity: Int = 2,
        parent: Job? = null,
        private val whenClosed: () -> Unit = {},
        private val whenStarted: () -> Unit = {}
    ) : TestActor, Actor(context, parent, channelCapacity = capacity) {

        private var isClosed = false

        override suspend fun expectedSequence(expected: Int) = act {
            expect(expected)
        }

        override suspend fun fail() = act {
            throw IOException()
        }

        override fun onStart() {
            whenStarted()
        }

        override fun onClose() {
            assertFalse(isClosed)
            isClosed = true
            whenClosed()
        }
    }

    private inner class ActTestActor(
        context: CoroutineContext,
        capacity: Int = 2,
        parent: Job? = null,
        private val whenClosed: () -> Unit = {},
        private val whenStarted: () -> Unit = {}
    ) : TypedActor<Any>(context, parent, channelCapacity = capacity), TestActor {

        private lateinit var launchedJob: Job
        private var isClosed = false

        override suspend fun receive(message: Any) {
            when (message) {
                is Int -> expect(message)
                is Throwable -> throw message
                else -> {
                    launchedJob = launch(coroutineContext) { while (true) yield() }
                }
            }
        }

        override fun onStart() {
            whenStarted()
        }

        override suspend fun expectedSequence(expected: Int) = send(expected)

        override suspend fun fail() = send(IOException())

        override fun onClose() {
            assertFalse(isClosed)
            isClosed = true
            whenClosed()
        }
    }

    @Test
    fun testClose() = runTest {
        val actor = TestActor(coroutineContext, 4)
        expect(1)
        actor.expectedSequence(2)
        actor.expectedSequence(3)
        actor.close()
        actor.join()
        finish(4)
    }

    @Test
    fun testOnClose() = runTest {
        val actor = TestActor(coroutineContext, 4, whenClosed = { expect(4) })
        expect(1)
        actor.expectedSequence(2)
        actor.expectedSequence(3)
        actor.close()
        actor.join()
        finish(5)
    }

    @Test
    fun testExternalJob() = runTest {
        val job = Job()
        val actor = TestActor(coroutineContext, parent = job, capacity = 1, whenClosed = { expect(6) })
        expect(1)
        actor.expectedSequence(2)
        actor.expectedSequence(3)
        expect(4)
        actor.expectedSequence(5)
        job.cancel()
        actor.join()
        finish(7)
    }

    @Test
    fun testExternalJobCancellation() = runTest(
        unhandled = unhandledFailures(3)
    ) {

        val job = launch(coroutineContext.minusKey(Job)) {
            expect(2)
            while (true) {
                yield()
            }
        }

        val actor = TestActor(coroutineContext, parent = job, capacity = 1)
        expect(1)
        actor.expectedSequence(3)
        yield()
        actor.fail()
        actor.join()
        assertTrue(job.isCompleted)
        finish(4)
    }

    @Test
    fun testExternalJobWithException() = runTest {
        val job = Job()
        val actor = TestActor(coroutineContext, parent = job, capacity = 1, whenClosed = { expect(6) })
        expect(1)
        actor.expectedSequence(2)
        actor.expectedSequence(3)
        expect(4)
        actor.expectedSequence(5)
        job.cancel(IOException())
        actor.join()
        finish(7)
    }

    @Test
    fun testCloseWithExternalJob() = runTest {
        val job = Job()
        val actor = TestActor(coroutineContext, parent = job, capacity = 1, whenClosed = { expect(6) })
        expect(1)
        actor.expectedSequence(2)
        actor.expectedSequence(3)
        expect(4)
        actor.expectedSequence(5)
        actor.close()
        actor.join()
        finish(7)
    }

    @Test
    fun testCancel() = runTest {
        val actor = TestActor(coroutineContext, 4)
        expect(1)
        actor.expectedSequence(2)
        actor.expectedSequence(3)
        actor.cancel()
        actor.join()
        finish(2)
    }

    @Test
    fun testOnCloseCancel() = runTest {
        val actor = TestActor(coroutineContext, 4, whenClosed = { expect(3) })
        expect(1)
        actor.expectedSequence(2)
        yield()
        actor.cancel()
        actor.join()
        finish(4)
    }

    @Test
    fun testOnCloseCancelNotStarted() = runTest {
        val actor = TestActor(coroutineContext, 4, whenClosed = { expect(2) })
        expect(1)
        actor.expectedSequence(2) // is not invoked
        actor.expectedSequence(3) // is not invoked
        actor.cancel()
        actor.join()
        finish(3)
    }

    @Test
    fun testOnCloseCloseNotStarted() = runTest {
        val actor = TestActor(coroutineContext, 4, whenClosed = { expect(2) })
        expect(1)
        actor.close()
        actor.join()
        finish(3)
    }

    @Test
    fun testClosedActorThrows() = runTest(expected = { it is ClosedSendChannelException }) {
        val actor = TestActor(coroutineContext)
        actor.close()
        actor.expectedSequence(1)
        expectUnreached()
    }

    @Test
    fun testOnStart() = runTest {
        val actor = TestActor(coroutineContext, whenStarted = { expect(1) })
        actor.expectedSequence(2)
        actor.close()
        actor.join()
        finish(3)
    }

    @Test
    fun testOnStartNotCalled() = runTest {
        val actor = TestActor(coroutineContext, whenStarted = { expectUnreached() })
        actor.cancel()
        actor.join()
        finish(1)
    }

    @Test
    fun testOnStartThrowing() = runTest(unhandled = unhandledFailures(2)) {
        val actor = TestActor(coroutineContext.minusKey(Job), whenStarted = { throw IOException() })
        actor.join()
    }

    @Test
    fun testActorUnhandledExceptions() = runTest(
        expected = { it is ClosedSendChannelException },
        unhandled = unhandledFailures(2)
    ) {
        val actor = TestActor(coroutineContext)
        actor.fail()
        yield()
        actor.expectedSequence(1)
        expectUnreached()
    }

    @Test
    fun testConflated() = runTest {
        val actor = TestActor(coroutineContext, capacity = Channel.CONFLATED)
        actor.expectedSequence(42)
        actor.expectedSequence(-1)
        actor.expectedSequence(1)
        yield()
        actor.close()
        actor.join()
        finish(2)
    }

    private fun unhandledFailures(count: Int): List<(Throwable) -> Boolean> {
        return MutableList(count) { { e: Throwable -> e is IOException } }
    }
}
