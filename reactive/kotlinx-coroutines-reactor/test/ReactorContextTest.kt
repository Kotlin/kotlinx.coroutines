package kotlinx.coroutines.reactor

import kotlinx.coroutines.*
import kotlinx.coroutines.reactive.*
import org.junit.Test
import reactor.util.context.Context
import kotlin.test.assertEquals

class ReactorContextTest {
    @Test
    fun testMonoHookedContext() = runBlocking {
        val mono = mono(Context.of(1, "1", 7, "7").asCoroutineContext()) {
            val ctx = coroutineContext[ReactorContext]?.context
            buildString {
                (1..7).forEach { append(ctx?.getOrDefault(it, "noValue")) }
            }
        }   .subscriberContext(Context.of(2, "2", 3, "3", 4, "4", 5, "5"))
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
}