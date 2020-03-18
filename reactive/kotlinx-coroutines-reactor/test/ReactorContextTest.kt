package kotlinx.coroutines.reactor

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.flow.*
import kotlinx.coroutines.reactive.*
import org.junit.Test
import reactor.core.publisher.*
import reactor.util.context.*
import kotlin.coroutines.*
import kotlin.test.*

class ReactorContextTest : TestBase() {
    @Test
    fun testMonoHookedContext() = runBlocking {
        val mono = mono(Context.of(1, "1", 7, "7").asCoroutineContext()) {
            val ctx = reactorContext()
            buildString {
                (1..7).forEach { append(ctx.getOrDefault(it, "noValue")) }
            }
        }  .subscriberContext(Context.of(2, "2", 3, "3", 4, "4", 5, "5"))
           .subscriberContext { ctx -> ctx.put(6, "6") }
        assertEquals(mono.awaitFirst(), "1234567")
    }

    @Test
    fun testFluxContext() {
        val flux = flux(Context.of(1, "1", 7, "7").asCoroutineContext()) {
            val ctx = reactorContext()
            (1..7).forEach { send(ctx.getOrDefault(it, "noValue")) }
        }
            .subscriberContext(Context.of(2, "2", 3, "3", 4, "4", 5, "5"))
            .subscriberContext { ctx -> ctx.put(6, "6") }
        val list = flux.collectList().block()!!
        assertEquals((1..7).map { it.toString() }, list)
    }

    @Test
    fun testAwait() = runBlocking(Context.of(3, "3").asCoroutineContext()) {
        val result = mono(Context.of(1, "1").asCoroutineContext()) {
            val ctx = reactorContext()
            buildString {
                (1..3).forEach { append(ctx.getOrDefault(it, "noValue")) }
            }
        }  .subscriberContext(Context.of(2, "2"))
            .awaitFirst()
        assertEquals(result, "123")
    }

    @Test
    fun testMonoAwaitContextPropagation() = runBlocking(Context.of(7, "7").asCoroutineContext()) {
        assertEquals(createMono().awaitFirst(), "7")
        assertEquals(createMono().awaitFirstOrDefault("noValue"), "7")
        assertEquals(createMono().awaitFirstOrNull(), "7")
        assertEquals(createMono().awaitFirstOrElse { "noValue" }, "7")
        assertEquals(createMono().awaitLast(), "7")
        assertEquals(createMono().awaitSingle(), "7")
    }

    @Test
    fun testFluxAwaitContextPropagation() = runBlocking<Unit>(
        Context.of(1, "1", 2, "2", 3, "3").asCoroutineContext()
    ) {
        assertEquals(createFlux().awaitFirst(), "1")
        assertEquals(createFlux().awaitFirstOrDefault("noValue"), "1")
        assertEquals(createFlux().awaitFirstOrNull(), "1")
        assertEquals(createFlux().awaitFirstOrElse { "noValue" }, "1")
        assertEquals(createFlux().awaitLast(), "3")
    }

    private fun createMono(): Mono<String> = mono {
        val ctx = reactorContext()
        ctx.getOrDefault(7, "noValue")
    }


    private fun createFlux(): Flux<String?> = flux {
        val ctx = reactorContext()
        (1..3).forEach { send(ctx.getOrDefault(it, "noValue")) }
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
        // convert resulting flow to channel using "produceIn"
        val channel = bar().produceIn(this)
        val list = channel.toList()
        assertEquals(listOf("1", "2", "3"), list)
    }

    private fun bar(): Flow<String> = flux {
        val ctx = reactorContext()
        (1..3).forEach { send(ctx.getOrDefault(it, "noValue")) }
    }.asFlow()

    private suspend fun reactorContext() =
        coroutineContext[ReactorContext]!!.context
}