package kotlinx.coroutines.rx2

import kotlinx.coroutines.testing.*
import io.reactivex.*
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlinx.coroutines.reactive.*
import org.junit.Test
import org.junit.runner.*
import org.junit.runners.*
import kotlin.coroutines.*
import kotlin.test.*

@RunWith(Parameterized::class)
class IntegrationTest(
    private val ctx: Ctx,
    private val delay: Boolean
) : TestBase() {

    enum class Ctx {
        MAIN        { override fun invoke(context: CoroutineContext): CoroutineContext = context.minusKey(Job) },
        DEFAULT     { override fun invoke(context: CoroutineContext): CoroutineContext = Dispatchers.Default },
        UNCONFINED  { override fun invoke(context: CoroutineContext): CoroutineContext = Dispatchers.Unconfined };

        abstract operator fun invoke(context: CoroutineContext): CoroutineContext
    }

    companion object {
        @Parameterized.Parameters(name = "ctx={0}, delay={1}")
        @JvmStatic
        fun params(): Collection<Array<Any>> = Ctx.values().flatMap { ctx ->
            listOf(false, true).map { delay ->
                arrayOf(ctx, delay)
            }
        }
    }

    @Test
    fun testEmpty(): Unit = runBlocking {
        val observable = rxObservable<String>(ctx(coroutineContext)) {
            if (delay) delay(1)
            // does not send anything
        }
        assertFailsWith<NoSuchElementException> { observable.awaitFirst() }
        assertEquals("OK", observable.awaitFirstOrDefault("OK"))
        assertNull(observable.awaitFirstOrNull())
        assertEquals("ELSE", observable.awaitFirstOrElse { "ELSE" })
        assertFailsWith<NoSuchElementException> { observable.awaitLast() }
        assertFailsWith<NoSuchElementException> { observable.awaitSingle() }
        var cnt = 0
        observable.collect {
            cnt++
        }
        assertEquals(0, cnt)
    }

    @Test
    fun testSingle() = runBlocking {
        val observable = rxObservable(ctx(coroutineContext)) {
            if (delay) delay(1)
            send("OK")
        }
        assertEquals("OK", observable.awaitFirst())
        assertEquals("OK", observable.awaitFirstOrDefault("OK"))
        assertEquals("OK", observable.awaitFirstOrNull())
        assertEquals("OK", observable.awaitFirstOrElse { "ELSE" })
        assertEquals("OK", observable.awaitLast())
        assertEquals("OK", observable.awaitSingle())
        var cnt = 0
        observable.collect {
            assertEquals("OK", it)
            cnt++
        }
        assertEquals(1, cnt)
    }

    @Test
    fun testNumbers() = runBlocking<Unit> {
        val n = 100 * stressTestMultiplier
        val observable = rxObservable(ctx(coroutineContext)) {
            for (i in 1..n) {
                send(i)
                if (delay) delay(1)
            }
        }
        assertEquals(1, observable.awaitFirst())
        assertEquals(1, observable.awaitFirstOrDefault(0))
        assertEquals(1, observable.awaitFirstOrNull())
        assertEquals(1, observable.awaitFirstOrElse { 0 })
        assertEquals(n, observable.awaitLast())
        assertFailsWith<IllegalArgumentException> { observable.awaitSingle() }
        checkNumbers(n, observable)
        val channel = observable.toChannel()
        checkNumbers(n, channel.consumeAsFlow().asObservable(ctx(coroutineContext)))
        channel.cancel()
    }

    @Test
    fun testCancelWithoutValue() = runTest {
        val job = launch(Job(), start = CoroutineStart.UNDISPATCHED) {
            rxObservable<String> {
                hang {  }
            }.awaitFirst()
        }

        job.cancel()
        job.join()
    }

    @Test
    fun testEmptySingle() = runTest(unhandled = listOf({e -> e is NoSuchElementException})) {
        expect(1)
        val job = launch(Job(), start = CoroutineStart.UNDISPATCHED) {
            rxObservable<String> {
                yield()
                expect(2)
                // Nothing to emit
            }.awaitFirst()
        }

        job.join()
        finish(3)
    }

    @Test
    fun testObservableWithTimeout() = runTest {
        val observable = rxObservable<Int> {
            expect(2)
            withTimeout(1) { delay(100) }
        }
        try {
            expect(1)
            observable.awaitFirstOrNull()
        } catch (e: CancellationException) {
            expect(3)
        }
        finish(4)
    }

    private suspend fun checkNumbers(n: Int, observable: Observable<Int>) {
        var last = 0
        observable.collect {
            assertEquals(++last, it)
        }
        assertEquals(n, last)
    }

}
