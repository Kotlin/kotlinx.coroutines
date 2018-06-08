package kotlinx.coroutines.experimental.actors

import kotlinx.coroutines.experimental.*
import org.junit.*
import org.junit.Test
import java.util.concurrent.*
import kotlin.test.*

class ActorSequentialProcessingStressTest : TestBase() {

    private val iterations = 10_000 * stressTestMultiplier
    private val senders = 4

    private val actorContext = newSingleThreadContext("Actor Stress Test")
    private val senderContext = newFixedThreadPoolContext(senders, "Actor Stress Test")

    @After
    fun tearDown() {
        actorContext.close()
        senderContext.close()
    }

    private inner class TestActor : Actor(actorContext) {
        var state = 0
        private var thread: Thread? = null

        suspend fun increment() = act {
            ++state
            if (thread == null) {
                thread = Thread.currentThread()
            } else {
                assertSame(thread, Thread.currentThread())
            }
        }
    }

    private inner class MonoTestActor : MonoActor<Unit>(actorContext) {
        var state = 0
        private var thread: Thread? = null

        override suspend fun receive(message: Unit) {
            ++state
            if (thread == null) {
                thread = Thread.currentThread()
            } else {
                assertSame(thread, Thread.currentThread())
            }
        }
    }

    @Test
    fun testActor() = runTest {
        val startBarrier = CyclicBarrier(5)

        val actor = TestActor()
        val tasks = (1..4).map {
            async(senderContext) {
                startBarrier.await()
                repeat(iterations) {
                    actor.increment()
                }
            }
        }

        startBarrier.await()
        tasks.awaitAll()
        actor.close()
        actor.join()
        assertEquals(senders * iterations * stressTestMultiplier, actor.state)
    }

    @Test
    fun testMonoActor() = runTest {
        val startBarrier = CyclicBarrier(5)

        val actor = MonoTestActor()
        val tasks = (1..4).map {
            async(senderContext) {
                startBarrier.await()
                repeat(iterations) {
                    actor.send(Unit)
                }
            }
        }

        startBarrier.await()
        tasks.awaitAll()
        actor.close()
        actor.join()
        assertEquals(senders * iterations * stressTestMultiplier, actor.state)
    }
}
