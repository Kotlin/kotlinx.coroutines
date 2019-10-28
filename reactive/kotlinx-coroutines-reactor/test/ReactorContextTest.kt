package kotlinx.coroutines.reactor

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.flow.*
import kotlinx.coroutines.reactive.*
import org.junit.Test
import reactor.core.publisher.*
import reactor.util.context.*
import kotlin.test.*

class ReactorContextTest {
    @Test
    fun testMonoHookedContext() = runBlocking {
        val mono = mono(Context.of(1, "1", 7, "7").asCoroutineContext()) {
            val ctx = coroutineContext[ReactorContext]?.context
            buildString {
                (1..7).forEach { append(ctx?.getOrDefault(it, "noValue")) }
            }
        }  .subscriberContext(Context.of(2, "2", 3, "3", 4, "4", 5, "5"))
           .subscriberContext { ctx -> ctx.put(6, "6") }
        assertEquals(mono.awaitFirst(), "1234567")
    }

    @Test
    fun testFluxContext() = runBlocking<Unit> {
        val flux = flux(Context.of(1, "1", 7, "7").asCoroutineContext()) {
            val ctx = coroutineContext[ReactorContext]!!.context
            (1..7).forEach { send(ctx.getOrDefault(it, "noValue")) }
        }   .subscriberContext(Context.of(2, "2", 3, "3", 4, "4", 5, "5"))
            .subscriberContext { ctx -> ctx.put(6, "6") }
        var i = 0
        flux.subscribe { str -> i++; assertEquals(str, i.toString()) }
    }

    @Test
    fun testAwait() = runBlocking(Context.of(3, "3").asCoroutineContext()) {
        val result = mono(Context.of(1, "1").asCoroutineContext()) {
            val ctx = coroutineContext[ReactorContext]?.context
            buildString {
                (1..3).forEach { append(ctx?.getOrDefault(it, "noValue")) }
            }
        }  .subscriberContext(Context.of(2, "2"))
            .awaitFirst()
        assertEquals(result, "123")
    }

    @Test
    fun testMonoAwaitContextPropagation() = runBlocking(Context.of(7, "7").asCoroutineContext()) {
        assertEquals(m().awaitFirst(), "7")
        assertEquals(m().awaitFirstOrDefault("noValue"), "7")
        assertEquals(m().awaitFirstOrNull(), "7")
        assertEquals(m().awaitFirstOrElse { "noValue" }, "7")
        assertEquals(m().awaitLast(), "7")
        assertEquals(m().awaitSingle(), "7")
    }

    @Test
    fun testFluxAwaitContextPropagation() = runBlocking<Unit>(
        Context.of(1, "1", 2, "2", 3, "3").asCoroutineContext()
    ) {
        assertEquals(f().awaitFirst(), "1")
        assertEquals(f().awaitFirstOrDefault("noValue"), "1")
        assertEquals(f().awaitFirstOrNull(), "1")
        assertEquals(f().awaitFirstOrElse { "noValue" }, "1")
        assertEquals(f().awaitLast(), "3")
        var i = 0
        f().subscribe { str -> i++; assertEquals(str, i.toString()) }
    }

    private fun m(): Mono<String> = mono {
        val ctx = coroutineContext[ReactorContext]?.context
        ctx?.getOrDefault(7, "noValue")
    }


    private fun f(): Flux<String?> = flux {
        val ctx = coroutineContext[ReactorContext]?.context
        (1..3).forEach { send(ctx?.getOrDefault(it, "noValue")) }
    }

    @Test
    fun testFlowToFluxContextPropagation() = runBlocking(
        Context.of(1, "1", 2, "2", 3, "3").asCoroutineContext()
    ) {
        var i = 0
        // call "collect" on the converted Flow
        bar().collect { str ->
            i++; assertEquals(str, i.toString())
        }
        assertEquals(i, 3)
    }

    @Test
    fun testFlowToFluxDirectContextPropagation() = runBlocking(
        Context.of(1, "1", 2, "2", 3, "3").asCoroutineContext()
    ) {
        var i = 0
        // convert resulting flow to channel using "produceIn"
        val channel = bar().produceIn(this)
        channel.consumeEach { str ->
            i++; assertEquals(str, i.toString())
        }
        assertEquals(i, 3)
    }

    private fun bar(): Flow<String> = flux {
        val ctx = coroutineContext[ReactorContext]!!.context
        (1..3).forEach { send(ctx.getOrDefault(it, "noValue")) }
    }.asFlow()
}