/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.jdk9

import kotlinx.coroutines.*
import kotlinx.coroutines.exceptions.*
import org.junit.Test
import kotlinx.coroutines.flow.flowOn
import org.junit.runner.*
import org.junit.runners.*
import kotlin.contracts.*
import java.util.concurrent.Flow as JFlow
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
        val pub = flowPublish<String>(ctx(coroutineContext)) {
            if (delay) delay(1)
            // does not send anything
        }
        assertFailsWith<NoSuchElementException> { pub.awaitFirst() }
        assertEquals("OK", pub.awaitFirstOrDefault("OK"))
        assertNull(pub.awaitFirstOrNull())
        assertEquals("ELSE", pub.awaitFirstOrElse { "ELSE" })
        assertFailsWith<NoSuchElementException> { pub.awaitLast() }
        assertFailsWith<NoSuchElementException> { pub.awaitSingle() }
        var cnt = 0
        pub.collect { cnt++ }
        assertEquals(0, cnt)
    }

    @Test
    fun testSingle() = runBlocking {
        val pub = flowPublish(ctx(coroutineContext)) {
            if (delay) delay(1)
            send("OK")
        }
        assertEquals("OK", pub.awaitFirst())
        assertEquals("OK", pub.awaitFirstOrDefault("!"))
        assertEquals("OK", pub.awaitFirstOrNull())
        assertEquals("OK", pub.awaitFirstOrElse { "ELSE" })
        assertEquals("OK", pub.awaitLast())
        assertEquals("OK", pub.awaitSingle())
        var cnt = 0
        pub.collect {
            assertEquals("OK", it)
            cnt++
        }
        assertEquals(1, cnt)
    }

    @Test
    fun testNumbers() = runBlocking {
        val n = 100 * stressTestMultiplier
        val pub = flowPublish(ctx(coroutineContext)) {
            for (i in 1..n) {
                send(i)
                if (delay) delay(1)
            }
        }
        assertEquals(1, pub.awaitFirst())
        assertEquals(1, pub.awaitFirstOrDefault(0))
        assertEquals(n, pub.awaitLast())
        assertEquals(1, pub.awaitFirstOrNull())
        assertEquals(1, pub.awaitFirstOrElse { 0 })
        assertFailsWith<IllegalArgumentException> { pub.awaitSingle() }
        checkNumbers(n, pub)
        val flow = pub.asFlow()
        checkNumbers(n, flow.flowOn(ctx(coroutineContext)).asPublisher())
    }

    @Test
    fun testCancelWithoutValue() = runTest {
        val job = launch(Job(), start = CoroutineStart.UNDISPATCHED) {
            flowPublish<String> {
                hang {}
            }.awaitFirst()
        }

        job.cancel()
        job.join()
    }

    @Test
    fun testEmptySingle() = runTest(unhandled = listOf { e -> e is NoSuchElementException}) {
        expect(1)
        val job = launch(Job(), start = CoroutineStart.UNDISPATCHED) {
            flowPublish<String> {
                yield()
                expect(2)
                // Nothing to emit
            }.awaitFirst()
        }

        job.join()
        finish(3)
    }

    private suspend fun checkNumbers(n: Int, pub: JFlow.Publisher<Int>) {
        var last = 0
        pub.collect {
            assertEquals(++last, it)
        }
        assertEquals(n, last)
    }

}

@OptIn(ExperimentalContracts::class)
internal suspend inline fun <reified E: Throwable> assertCallsExceptionHandlerWith(
    crossinline operation: suspend (CoroutineExceptionHandler) -> Unit): E {
    contract {
        callsInPlace(operation, InvocationKind.EXACTLY_ONCE)
    }
    val handler = CapturingHandler()
    return withContext(handler) {
        operation(handler)
        handler.getException().let {
            assertTrue(it is E, it.toString())
            it
        }
    }
}
