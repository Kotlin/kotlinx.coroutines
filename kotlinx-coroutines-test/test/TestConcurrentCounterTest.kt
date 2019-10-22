package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.Channel
import kotlinx.coroutines.channels.ReceiveChannel
import kotlinx.coroutines.channels.SendChannel
import kotlinx.coroutines.selects.select
import org.junit.Assert.assertEquals
import org.junit.Test
import java.security.NoSuchAlgorithmException
import java.security.SecureRandom
import java.util.*
import java.util.concurrent.TimeUnit

class TestConcurrentCounterTest {

    /*
     This coroutine is a storage location.
     */
    fun CoroutineScope.launchRegister(
            readChannel: ReceiveChannel<CompletableDeferred<Int>>,
            writeChannel: ReceiveChannel<Int>
    ): Job = launch {
        var storageLocation: Int = 0
        while (true)
            select<Unit> {
                readChannel.onReceive {
                    it.complete(storageLocation)
                }
                writeChannel.onReceive {
                    storageLocation = it
                }
            }
    }

    /*
     This coroutine does read-increment-write. It's buggy!
     */
    fun CoroutineScope.launchIncrementer(
            n: Int,
            writeChannel: SendChannel<Int>,
            readChannel: SendChannel<CompletableDeferred<Int>>): Job = launch {
        repeat(n) {
            val futureValue = CompletableDeferred<Int>()
            readChannel.send(futureValue)
            val oldValue = futureValue.await()
            val newValue = oldValue + 1
            writeChannel.send(newValue)
        }
    }

    /*
     Run the nondeterministic test N times to demonstrate its nondeterminism.
     In my experiments, this test usually fails, but you can't be sure it will _always_ do so.
     */
    @Test
    fun nondeterministicTestN() = runBlocking {

        val readChannel = Channel<CompletableDeferred<Int>>()
        val writeChannel = Channel<Int>()

        var successes = 0
        val N = 100

        repeat(N) {
            if (nondeterministicTestOnce(readChannel, writeChannel))
                successes++
        }
        assertEquals(N, successes)
    }

    /*
     This nondeterministic "test" is obviously flaky. It sometimes returns true and other times
     returns false (indicating that the "unit under test" failed).
     The "unit under test" (the incrementer coroutines interacting with the register one)
     is obviously buggy. We'd like a test that flags the a failure every time it's run.
     */
    private suspend fun nondeterministicTestOnce(readChannel: Channel<CompletableDeferred<Int>>, writeChannel: Channel<Int>): Boolean {

        val result: Boolean

        val register: Job

        with(GlobalScope) {
            register = launchRegister(readChannel, writeChannel)
            val a = launchIncrementer(1, writeChannel, readChannel)
            val b = launchIncrementer(1, writeChannel, readChannel)
            joinAll(a, b)
        }

        val futureVal = CompletableDeferred<Int>()
        readChannel.send(futureVal)

        result = futureVal.await() == 2

        register.cancelAndJoin()

        return result
    }

    /*
     Here is the corresponding deterministic test. It always passes, which is unfortunate
     since the "unit under test" is buggy, as (usually) demonstrated  by the nondeterministic
     test above.
     */
    @Test
    fun deterministicTestN() = runBlockingTest {
        val readChannel = Channel<CompletableDeferred<Int>>()
        val writeChannel = Channel<Int>()

        var successes = 0
        val N = 100

        repeat(N) {
            if (deterministicTestOnce(readChannel, writeChannel))
                successes++
        }
        assertEquals(N, successes)
    }

    private suspend fun TestCoroutineScope.deterministicTestOnce(
            readChannel: Channel<CompletableDeferred<Int>>,
            writeChannel: Channel<Int>): Boolean {

        val register = launchRegister(readChannel, writeChannel)
        val a = launchIncrementer(1, writeChannel, readChannel)
        val b = launchIncrementer(1, writeChannel, readChannel)

        joinAll(a, b)
        advanceUntilIdle()

        val futureVal = CompletableDeferred<Int>()
        readChannel.send(futureVal)

        advanceUntilIdle()

        return (futureVal.await() == 2).also {
            register.cancelAndJoin()
        }
    }

    /*
     This deterministic test uses the proposed settings on TestCoroutineScope
     to establish a TestCoroutineDispatcher that skews scheduled run-times for
     tasks.

     This test operates in two different modes depending on the exploreInterleavings
     parameter on createRandom(). When that's true, each call to createRandom() uses
     a new seed derived from the system clock. When it's false, the value of the
     trySeed parameter is used as the seed to "lock down" the pseudo-random number
     generator.
     */
    @Test
    fun deterministicInaccurateDispatcherTestN() {
        val readChannel = Channel<CompletableDeferred<Int>>()
        val writeChannel = Channel<Int>()

        var successes = 0
        val N = 100

        repeat(N) {

            // lock the PRNG down to a value that always passes
//            val random = createRandom(418_996_022_289_704L, false)

            // lock the PRNG down to a value that always FAILS
            val random = createRandom(420_864_149_765_280L, false)

            // alternately, have createRandom() use a new seed derived from the system clock
            // this is useful for exploring various interleavings
//            val random = createRandom(418_996_022_289_704L, true)

            val testCoroutineScope =
                    TestCoroutineScope(
                            random = random,
                            standardDeviation = 10,
                            standardDeviationUnit = TimeUnit.MILLISECONDS)
            testCoroutineScope.runBlockingTest {
                pauseDispatcher() {
                    if (deterministicTestOnce(readChannel, writeChannel)) {
                        successes++
                        println("success!")
                    }
                }
            }
        }
        assertEquals(N, successes)
    }

    fun createRandom(trySeed: Long, exploreInterleavings: Boolean): Random {

        val actualSeed: Long

        if (exploreInterleavings)
            actualSeed = System.nanoTime()
        else
            actualSeed = trySeed

        println(String.format("using seed %,d", actualSeed))

        try {
            return SecureRandom.getInstance("SHA1PRNG").also {
                it.setSeed(actualSeed)
            }
        } catch (e: NoSuchAlgorithmException) {
            throw AssertionError(e)
        }

    }

}