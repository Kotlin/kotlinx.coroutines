package kotlinx.coroutines.experimental.actors

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.channels.*
import org.junit.Test
import org.junit.runner.*
import org.junit.runners.*
import java.io.*
import kotlin.coroutines.experimental.*
import kotlin.test.*

@RunWith(Parameterized::class) // Base operations for all types of actor
class ActorsBaseTest(private val actorType: ActorType) : TestBase() {

    companion object {
        @Parameterized.Parameters(name = "{0}")
        @JvmStatic
        fun params(): Collection<Array<Any>> =
            ActorType.values().map { arrayOf<Any>(it) }
    }

    enum class ActorType {
        SINGLE_METHOD,
        MULTI_METHOD,
        PARALLEL
    }

    private fun TestActor(
        context: CoroutineContext,
        capacity: Int = 2, parent: Job? = null,
        whenClosed: () -> Unit = {}
    ): TestActor {
        return when (actorType) {
            ActorType.SINGLE_METHOD -> SingleMethodActor(context, capacity, parent, whenClosed)
            ActorType.MULTI_METHOD -> MultiMethodActor(context, capacity, parent, whenClosed)
            else -> workerPool(1, parent) { ParallelTestActor(context, capacity, whenClosed) }
        }
    }

    interface TestActor {
        suspend fun expectedSequence(expected: Int)
        suspend fun launchChild()
        suspend fun getChild(): Job

        public fun close()
        public fun kill()
        public suspend fun join()
    }

    inner class MultiMethodActor(
        context: CoroutineContext,
        capacity: Int = 2,
        parent: Job? = null,
        private val whenClosed: () -> Unit = {}
    ) : TestActor, Actor(context, parent, channelCapacity = capacity) {

        private lateinit var launchedJob: Job
        private var isClosed = false

        override suspend fun expectedSequence(expected: Int) = act {
            expect(expected)
        }

        override suspend fun launchChild() = act {
            launchedJob = launch(actorContext) { while (true) yield() }
        }

        override suspend fun getChild(): Job {
            yield()
            return launchedJob
        }

        override fun onClose() {
            assertFalse(isClosed)
            isClosed = true
            whenClosed()
        }
    }

    inner class SingleMethodActor(
        context: CoroutineContext,
        capacity: Int = 2,
        parent: Job? = null,
        private val whenClosed: () -> Unit = {}
    ) : MonoActor<Any>(context, parent, channelCapacity = capacity), TestActor {

        private lateinit var launchedJob: Job
        private var isClosed = false

        override suspend fun receive(message: Any) {
            when (message) {
                is Int -> expect(message)
                else -> {
                    launchedJob = launch(actorContext) { while (true) yield() }
                }
            }
        }

        override suspend fun expectedSequence(expected: Int) = send(expected)

        override suspend fun launchChild() = send(Unit)

        override suspend fun getChild(): Job {
            yield()
            return launchedJob
        }

        override fun onClose() {
            assertFalse(isClosed)
            isClosed = true
            whenClosed()
        }
    }


    // Global static
    private lateinit var `$parallelActorLaunchedJob`: Job

    inner class ParallelTestActor(
        context: CoroutineContext,
        capacity: Int = 2,
        private val whenClosed: () -> Unit = {}
    ) : WorkerPoolActor<ParallelTestActor>(context, workerChannelCapacity = capacity), TestActor {

        private var isClosed = false

        override suspend fun expectedSequence(expected: Int) = act {
            expect(expected)
        }

        override suspend fun launchChild() = act {
            `$parallelActorLaunchedJob` = launch(actorContext) { while (true) yield() }
        }

        override suspend fun getChild(): Job {
            yield()
            return `$parallelActorLaunchedJob`
        }

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
    fun testKill() = runTest {
        val actor = TestActor(coroutineContext, 4)
        expect(1)
        actor.expectedSequence(2)
        actor.expectedSequence(3)
        actor.kill()
        actor.join()
        finish(2)
    }

    @Test
    fun testKillOnClose() = runTest {
        val actor = TestActor(coroutineContext, 4, whenClosed = { expect(2) })
        expect(1)
        actor.expectedSequence(2)
        actor.expectedSequence(3)
        actor.kill()
        actor.join()
        finish(3)
    }

    @Test
    fun testParentChildLaunch() = runTest {
        val actor = TestActor(coroutineContext)
        actor.launchChild()
        assertTrue(actor.getChild().isActive)
        actor.close()
        actor.join()
        assertTrue(actor.getChild().isCancelled)
    }

    @Test
    fun testClosedActorThrows() = runTest(expected = { it is ClosedSendChannelException }) {
        val actor = TestActor(coroutineContext)
        actor.close()
        actor.expectedSequence(1)
    }
}
