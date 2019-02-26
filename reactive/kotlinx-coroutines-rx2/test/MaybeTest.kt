/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.rx2

import io.reactivex.*
import io.reactivex.functions.*
import io.reactivex.internal.functions.Functions.*
import kotlinx.coroutines.*
import org.hamcrest.core.*
import org.junit.*
import org.junit.Assert.*
import java.util.concurrent.*
import java.util.concurrent.CancellationException

class MaybeTest : TestBase() {
    @Before
    fun setup() {
        ignoreLostThreads("RxComputationThreadPool-", "RxCachedWorkerPoolEvictor-", "RxSchedulerPurge-")
    }

    @Test
    fun testBasicSuccess() = runBlocking {
        expect(1)
        val maybe = rxMaybe {
            expect(4)
            "OK"
        }
        expect(2)
        maybe.subscribe { value ->
            expect(5)
            Assert.assertThat(value, IsEqual("OK"))
        }
        expect(3)
        yield() // to started coroutine
        finish(6)
    }

    @Test
    fun testBasicEmpty() = runBlocking {
        expect(1)
        val maybe = rxMaybe {
            expect(4)
            null
        }
        expect(2)
        maybe.subscribe (emptyConsumer(), ON_ERROR_MISSING, Action {
            expect(5)
        })
        expect(3)
        yield() // to started coroutine
        finish(6)
    }

    @Test
    fun testBasicFailure() = runBlocking {
        expect(1)
        val maybe = rxMaybe(NonCancellable) {
            expect(4)
            throw RuntimeException("OK")
        }
        expect(2)
        maybe.subscribe({
            expectUnreached()
        }, { error ->
            expect(5)
            Assert.assertThat(error, IsInstanceOf(RuntimeException::class.java))
            Assert.assertThat(error.message, IsEqual("OK"))
        })
        expect(3)
        yield() // to started coroutine
        finish(6)
    }


    @Test
    fun testBasicUnsubscribe() = runBlocking {
        expect(1)
        val maybe = rxMaybe {
            expect(4)
            yield() // back to main, will get cancelled
            expectUnreached()
        }
        expect(2)
        // nothing is called on a disposed rx2 maybe
        val sub = maybe.subscribe({
            expectUnreached()
        }, {
            expectUnreached()
        })
        expect(3)
        yield() // to started coroutine
        expect(5)
        sub.dispose() // will cancel coroutine
        yield()
        finish(6)
    }

    @Test
    fun testMaybeNoWait() {
        val maybe = GlobalScope.rxMaybe {
            "OK"
        }

        checkMaybeValue(maybe) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testMaybeAwait() = runBlocking {
        assertEquals("OK", Maybe.just("O").await() + "K")
    }

    @Test
    fun testMaybeAwaitForNull() = runBlocking {
        assertNull(Maybe.empty<String>().await())
    }

    @Test
    fun testMaybeEmitAndAwait() {
        val maybe = GlobalScope.rxMaybe {
            Maybe.just("O").await() + "K"
        }

        checkMaybeValue(maybe) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testMaybeWithDelay() {
        val maybe = GlobalScope.rxMaybe {
            Observable.timer(50, TimeUnit.MILLISECONDS).map { "O" }.awaitSingle() + "K"
        }

        checkMaybeValue(maybe) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testMaybeException() {
        val maybe = GlobalScope.rxMaybe {
            Observable.just("O", "K").awaitSingle() + "K"
        }

        checkErroneous(maybe) {
            assert(it is IllegalArgumentException)
        }
    }

    @Test
    fun testAwaitFirst() {
        val maybe = GlobalScope.rxMaybe {
            Observable.just("O", "#").awaitFirst() + "K"
        }

        checkMaybeValue(maybe) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testAwaitLast() {
        val maybe = GlobalScope.rxMaybe {
            Observable.just("#", "O").awaitLast() + "K"
        }

        checkMaybeValue(maybe) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testExceptionFromObservable() {
        val maybe = GlobalScope.rxMaybe {
            try {
                Observable.error<String>(RuntimeException("O")).awaitFirst()
            } catch (e: RuntimeException) {
                Observable.just(e.message!!).awaitLast() + "K"
            }
        }

        checkMaybeValue(maybe) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testExceptionFromCoroutine() {
        val maybe = GlobalScope.rxMaybe<String> {
            throw IllegalStateException(Observable.just("O").awaitSingle() + "K")
        }

        checkErroneous(maybe) {
            assert(it is IllegalStateException)
            assertEquals("OK", it.message)
        }
    }

    @Test
    fun testCancelsParentOnFailure() = runTest(
        expected = { it is RuntimeException && it.message == "OK" }
    ) {
        // has parent, so should cancel it on failure
        rxMaybe<Unit> {
            throw RuntimeException("OK")
        }.subscribe(
            { expectUnreached() },
            { assert(it is RuntimeException) }
        )
    }

    @Test
    fun testCancelledConsumer() = runTest {
        expect(1)
        val maybe = rxMaybe<Int> {
            expect(4)
            try {
                delay(Long.MAX_VALUE)
            } catch (e: CancellationException) {
                expect(6)
            }
            42
        }
        expect(2)
        val timeout = withTimeoutOrNull(100) {
            expect(3)
            maybe.consumeEach {
                expectUnreached()
            }
            expectUnreached()
        }
        assertNull(timeout)
        expect(5)
        yield() // must cancel code inside maybe!!!
        finish(7)
    }
}
