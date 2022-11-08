package kotlinx.coroutines.reactor

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlinx.coroutines.reactive.*
import org.junit.Test
import org.reactivestreams.*
import reactor.core.publisher.*
import reactor.util.context.Context
import java.util.concurrent.*
import kotlin.test.*

@Suppress("ReactiveStreamsSubscriberImplementation")
class FlowAsFluxTest : TestBase() {
    @Test
    fun testFlowAsFluxContextPropagation() {
        val flux = flow {
            (1..4).forEach { i -> emit(createMono(i).awaitSingle()) }
        }
            .asFlux()
            .contextWrite(Context.of(1, "1"))
            .contextWrite(Context.of(2, "2", 3, "3", 4, "4"))
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
            .contextWrite { ctx ->
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
            .contextWrite { ctx ->
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

    @Test
    fun testUnconfinedDefaultContext() {
        expect(1)
        val thread = Thread.currentThread()
        fun checkThread() {
            assertSame(thread, Thread.currentThread())
        }
        flowOf(42).asFlux().subscribe(object : Subscriber<Int> {
            private lateinit var subscription: Subscription

            override fun onSubscribe(s: Subscription) {
                expect(2)
                subscription = s
                subscription.request(2)
            }

            override fun onNext(t: Int) {
                checkThread()
                expect(3)
                assertEquals(42, t)
            }

            override fun onComplete() {
                checkThread()
                expect(4)
            }

            override fun onError(t: Throwable?) {
                expectUnreached()
            }
        })
        finish(5)
    }

    @Test
    fun testConfinedContext() {
        expect(1)
        val threadName = "FlowAsFluxTest.testConfinedContext"
        fun checkThread() {
            val currentThread = Thread.currentThread()
            assertTrue(currentThread.name.startsWith(threadName), "Unexpected thread $currentThread")
        }
        val completed = CountDownLatch(1)
        newSingleThreadContext(threadName).use { dispatcher ->
            flowOf(42).asFlux(dispatcher).subscribe(object : Subscriber<Int> {
                private lateinit var subscription: Subscription

                override fun onSubscribe(s: Subscription) {
                    expect(2)
                    subscription = s
                    subscription.request(2)
                }

                override fun onNext(t: Int) {
                    checkThread()
                    expect(3)
                    assertEquals(42, t)
                }

                override fun onComplete() {
                    checkThread()
                    expect(4)
                    completed.countDown()
                }

                override fun onError(t: Throwable?) {
                    expectUnreached()
                }
            })
            completed.await()
        }
        finish(5)
    }
}
