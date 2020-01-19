/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.rx2

import io.reactivex.Observable
import io.reactivex.subjects.PublishSubject
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.flow.*
import kotlin.test.*

class ObservableAsFlow3Test : TestBase() {
    @Test
    fun testCancellation() = runTest {
        var onNext = 0
        var onCancelled = 0
        var onError = 0

        val source = rxObservable(currentDispatcher()) {
            coroutineContext[Job]?.invokeOnCompletion {
                if (it is CancellationException) ++onCancelled
            }

            repeat(100) {
                send(it)
            }
        }

        source.asFlow3().launchIn(CoroutineScope(Dispatchers.Unconfined)) {
            onEach {
                ++onNext
                throw RuntimeException()
            }
            catch<Throwable> {
                ++onError
            }
        }.join()


        assertEquals(1, onNext)
        assertEquals(1, onError)
        assertEquals(1, onCancelled)
    }

    @Test
    fun testImmediateCollection() {
        val source = PublishSubject.create<Int>()
        val flow = source.asFlow3()
        GlobalScope.launch(Dispatchers.Unconfined) {
            expect(1)
            flow.collect { expect(it) }
            expect(6)
        }
        expect(2)
        source.onNext(3)
        expect(4)
        source.onNext(5)
        source.onComplete()
        finish(7)
    }

    @Test
    fun testOnErrorCancellation() {
        val source = PublishSubject.create<Int>()
        val flow = source.asFlow3()
        val exception = RuntimeException()
        GlobalScope.launch(Dispatchers.Unconfined) {
            try {
                expect(1)
                flow.collect { expect(it) }
                expectUnreached()
            }
            catch (e: Exception) {
                assertSame(exception, e.cause)
                expect(5)
            }
            expect(6)
        }
        expect(2)
        source.onNext(3)
        expect(4)
        source.onError(exception)
        finish(7)
    }

    @Test
    fun testUnsubscribeOnCollectionException() {
        val source = PublishSubject.create<Int>()
        val flow = source.asFlow3()
        val exception = RuntimeException()
        GlobalScope.launch(Dispatchers.Unconfined) {
            try {
                expect(1)
                flow.collect {
                    expect(it)
                    if (it == 3) throw exception
                }
                expectUnreached()
            }
            catch (e: Exception) {
                assertSame(exception, e.cause)
                expect(4)
            }
            expect(5)
        }
        expect(2)
        assertTrue(source.hasObservers())
        source.onNext(3)
        assertFalse(source.hasObservers())
        finish(6)
    }

    @Test
    fun testBufferUnlimited() = runTest {
        val source = rxObservable(currentDispatcher()) {
            expect(1); send(10)
            expect(2); send(11)
            expect(3); send(12)
            expect(4); send(13)
            expect(5); send(14)
            expect(6); send(15)
            expect(7); send(16)
            expect(8); send(17)
            expect(9)
        }
        source.asFlow3().buffer(Channel.UNLIMITED).collect { expect(it) }
        finish(18)
    }

    @Test
    fun testConflated() = runTest {
        val source = Observable.range(1, 5)
        val list = source.asFlow3().conflate().toList()
        assertEquals(listOf(1, 5), list)
    }

    @Test
    fun testProduce() = runTest {
        val source = Observable.range(0, 10)
        val flow = source.asFlow3()
        check((0..9).toList(), flow.produceIn(this))
        check((0..9).toList(), flow.buffer(Channel.UNLIMITED).produceIn(this))
        check((0..2).toList(), flow.buffer(2).produceIn(this))
            // whole source is "offered" immediately (no back-pressure), so 3..9 is dropped
        check(listOf(0, 9), flow.conflate().produceIn(this))
    }

    private suspend fun check(expected: List<Int>, channel: ReceiveChannel<Int>) {
        val result = ArrayList<Int>(10)
        channel.consumeEach { result.add(it) }
        assertEquals(expected, result)
    }
}