package kotlinx.coroutines.reactor

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlinx.coroutines.reactive.*
import org.junit.Test
import reactor.core.publisher.*
import reactor.util.context.Context
import kotlin.test.*

class FlowAsFluxTest : TestBase() {
    @Test
    fun testFlowAsFluxContextPropagation() {
        val flux = flow<String> {
            (1..4).forEach { i -> emit(createMono(i).awaitFirst()) }
        }
            .asFlux()
            .subscriberContext(Context.of(1, "1"))
            .subscriberContext(Context.of(2, "2", 3, "3", 4, "4"))
        val list = flux.collectList().block()!!
        assertEquals(listOf("1", "2", "3", "4"), list)
    }

    private fun createMono(i: Int): Mono<String> = mono {
        val ctx = coroutineContext[ReactorContext]!!.context
        ctx.getOrDefault(i, "noValue")
    }

    @Test
    fun testFluxAsFlowContextPropagationWithFlowOn() = runTest {
        expect(1)
        Flux.create<String> {
            it.next("OK")
            it.complete()
        }
            .subscriberContext { ctx ->
                expect(2)
                assertEquals("CTX", ctx.get(1))
                ctx
            }
            .asFlow()
            .flowOn(ReactorContext(Context.of(1, "CTX")))
            .collect {
                expect(3)
                assertEquals("OK", it)
            }
        finish(4)
    }

    @Test
    fun testFluxAsFlowContextPropagationFromScope() = runTest {
        expect(1)
        withContext(ReactorContext(Context.of(1, "CTX"))) {
            Flux.create<String> {
                    it.next("OK")
                    it.complete()
                }
            .subscriberContext { ctx ->
                expect(2)
                assertEquals("CTX", ctx.get(1))
                ctx
            }
            .asFlow()
            .collect {
                expect(3)
                assertEquals("OK", it)
            }
        }
        finish(4)
    }
}