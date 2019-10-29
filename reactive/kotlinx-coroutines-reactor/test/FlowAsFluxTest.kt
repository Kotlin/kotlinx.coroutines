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
    fun testFlowToFluxContextPropagation() = runBlocking<Unit> {
        val flux = flow<String> {
            (1..4).forEach { i -> emit(m(i).awaitFirst()) }
        }   .asFlux()
            .subscriberContext(Context.of(1, "1"))
            .subscriberContext(Context.of(2, "2", 3, "3", 4, "4"))
        var i = 0
        flux.subscribe { str -> i++; println(str); assertEquals(str, i.toString()) }
    }

    private fun m(i: Int): Mono<String> = mono {
        val ctx = coroutineContext[ReactorContext]?.context
        ctx?.getOrDefault(i, "noValue")
    }
}