package kotlinx.coroutines.reactor

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlinx.coroutines.reactive.*
import org.junit.Test
import reactor.core.publisher.Mono
import reactor.util.context.Context
import kotlin.test.assertEquals

class FlowAsFluxTest : TestBase() {
    @Test
    fun testFlowToFluxContextPropagation() {
        val flux = flow<String> {
            (1..4).forEach { i -> emit(createMono(i).awaitFirst()) }
        }   .asFlux()
            .subscriberContext(Context.of(1, "1"))
            .subscriberContext(Context.of(2, "2", 3, "3", 4, "4"))
        val list = flux.collectList().block()!!
        assertEquals(listOf("1", "2", "3", "4"), list)
    }

    private fun createMono(i: Int): Mono<String> = mono {
        val ctx = coroutineContext[ReactorContext]!!.context
        ctx.getOrDefault(i, "noValue")
    }
}