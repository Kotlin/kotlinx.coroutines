package kotlinx.coroutines

import kotlinx.coroutines.channels.*
import kotlinx.coroutines.testing.*
import java.util.concurrent.CyclicBarrier
import java.util.concurrent.atomic.*
import kotlin.test.*
import kotlin.time.Duration.Companion.seconds

class JobOnCompletionStressTest: TestBase() {
    private val N_ITERATIONS = 10_000 * stressTestMultiplier
    private val pool = newFixedThreadPoolContext(2, "JobOnCompletionStressTest")

    private val completionHandlerSeesCompletedParent = AtomicBoolean(false)
    private val completionHandlerSeesCancelledParent = AtomicBoolean(false)
    private val encounteredException = AtomicReference<Throwable?>(null)

    @AfterTest
    fun tearDown() {
        pool.close()
    }

    @Test
    fun testOnCompletionRacingWithCompletion() = runTest {
        testHandlerRacingWithCancellation(
            onCancelling = false,
            invokeImmediately = true,
            parentCompletion = { complete(Unit) }
        ) {
            assertNull(encounteredException.get())
            assertTrue(completionHandlerSeesCompletedParent.get())
            assertFalse(completionHandlerSeesCancelledParent.get())
        }
    }

    @Test
    fun testOnCompletionRacingWithCancellation() = runTest {
        testHandlerRacingWithCancellation(
            onCancelling = false,
            invokeImmediately = true,
            parentCompletion = { completeExceptionally(TestException()) }
        ) {
            assertIs<TestException>(encounteredException.get())
            assertTrue(completionHandlerSeesCompletedParent.get())
            assertTrue(completionHandlerSeesCancelledParent.get())
        }
    }

    @Test
    fun testOnCancellingRacingWithCompletion() = runTest {
        testHandlerRacingWithCancellation(
            onCancelling = true,
            invokeImmediately = true,
            parentCompletion = { complete(Unit) }
        ) {
            assertNull(encounteredException.get())
            assertTrue(completionHandlerSeesCompletedParent.get())
            assertFalse(completionHandlerSeesCancelledParent.get())
        }
    }

    @Test
    fun testOnCancellingRacingWithCancellation() = runTest {
        testHandlerRacingWithCancellation(
            onCancelling = true,
            invokeImmediately = true,
            parentCompletion = { completeExceptionally(TestException()) }
        ) {
            assertIs<TestException>(encounteredException.get())
            assertTrue(completionHandlerSeesCancelledParent.get())
        }
    }

    @Test
    fun testNonImmediateOnCompletionRacingWithCompletion() = runTest {
        testHandlerRacingWithCancellation(
            onCancelling = false,
            invokeImmediately = false,
            parentCompletion = { complete(Unit) }
        ) {
            assertNull(encounteredException.get())
            assertTrue(completionHandlerSeesCompletedParent.get())
            assertFalse(completionHandlerSeesCancelledParent.get())
        }
    }

    @Test
    fun testNonImmediateOnCompletionRacingWithCancellation() = runTest {
        testHandlerRacingWithCancellation(
            onCancelling = false,
            invokeImmediately = false,
            parentCompletion = { completeExceptionally(TestException()) }
        ) {
            assertIs<TestException>(encounteredException.get())
            assertTrue(completionHandlerSeesCompletedParent.get())
            assertTrue(completionHandlerSeesCancelledParent.get())
        }
    }

    @Test
    fun testNonImmediateOnCancellingRacingWithCompletion() = runTest {
        testHandlerRacingWithCancellation(
            onCancelling = true,
            invokeImmediately = false,
            parentCompletion = { complete(Unit) }
        ) {
            assertNull(encounteredException.get())
            assertTrue(completionHandlerSeesCompletedParent.get())
            assertFalse(completionHandlerSeesCancelledParent.get())
        }
    }

    @Test
    fun testNonImmediateOnCancellingRacingWithCancellation() = runTest {
        testHandlerRacingWithCancellation(
            onCancelling = true,
            invokeImmediately = false,
            parentCompletion = { completeExceptionally(TestException()) }
        ) {
            assertIs<TestException>(encounteredException.get())
            assertTrue(completionHandlerSeesCancelledParent.get())
        }
    }

    private suspend fun testHandlerRacingWithCancellation(
        onCancelling: Boolean,
        invokeImmediately: Boolean,
        parentCompletion: CompletableDeferred<Unit>.() -> Unit,
        validate: () -> Unit,
    ) {
        repeat(N_ITERATIONS) {
            val entered = Channel<Unit>(1)
            completionHandlerSeesCompletedParent.set(false)
            completionHandlerSeesCancelledParent.set(false)
            encounteredException.set(null)
            val parent = createCompletableDeferredForTesting(it)
            val barrier = CyclicBarrier(2)
            val handlerInstallJob = coroutineScope {
                launch(pool) {
                    barrier.await()
                    parent.parentCompletion()
                }
                async(pool) {
                    barrier.await()
                    parent.invokeOnCompletion(
                        onCancelling = onCancelling,
                        invokeImmediately = invokeImmediately,
                    ) { exception ->
                        encounteredException.set(exception)
                        completionHandlerSeesCompletedParent.set(parent.isCompleted)
                        completionHandlerSeesCancelledParent.set(parent.isCancelled)
                        entered.trySend(Unit)
                    }
                }
            }
            if (invokeImmediately || handlerInstallJob.getCompleted() !== NonDisposableHandle) {
                withTimeout(1.seconds) {
                    entered.receive()
                }
                try {
                    validate()
                } catch (e: Throwable) {
                    println("Iteration $it failed")
                    println("invokeOnCompletion returned ${handlerInstallJob.getCompleted()}")
                    throw e
                }
            } else {
                assertTrue(entered.isEmpty)
            }
        }
    }
}

/**
 * Creates a [CompletableDeferred], optionally adding completion handlers and/or other children to the job depending
 * on [iteration].
 * The purpose is to test not just attaching completion handlers to empty or one-element lists (see the [JobSupport]
 * implementation for details on what this means), but also to lists with multiple elements.
 */
fun createCompletableDeferredForTesting(iteration: Int): CompletableDeferred<Unit> {
    val parent = CompletableDeferred<Unit>()
    /* We optionally add completion handlers and/or other children to the parent job
       to test the scenarios where a child is placed into an empty list, a single-element list,
       or a list with multiple elements. */
    if (iteration.mod(2) == 0) {
        parent.invokeOnCompletion { }
    }
    if (iteration.mod(3) == 0) {
        GlobalScope.launch(parent) { }
    }
    return parent
}
