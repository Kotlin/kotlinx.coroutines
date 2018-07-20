/*
 * Copyright 2016-2017 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package kotlinx.coroutines.experimental.rx2

import io.reactivex.*
import kotlinx.coroutines.experimental.*
import org.hamcrest.core.*
import org.junit.*
import org.junit.Assert.*
import java.util.concurrent.*
import kotlin.coroutines.experimental.*

/**
 * Tests emitting single item with [rxSingle].
 */
class SingleTest : TestBase() {
    @Before
    fun setup() {
        ignoreLostThreads("RxComputationThreadPool-", "RxCachedWorkerPoolEvictor-", "RxSchedulerPurge-")
    }

    @Test
    fun testBasicSuccess() = runBlocking<Unit> {
        expect(1)
        val single = rxSingle(coroutineContext) {
            expect(4)
            "OK"
        }
        expect(2)
        single.subscribe { value ->
            expect(5)
            Assert.assertThat(value, IsEqual("OK"))
        }
        expect(3)
        yield() // to started coroutine
        finish(6)
    }

    @Test
    fun testBasicFailure() = runBlocking<Unit> {
        expect(1)
        val single = rxSingle(coroutineContext) {
            expect(4)
            throw RuntimeException("OK")
        }
        expect(2)
        single.subscribe({
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
    fun testBasicUnsubscribe() = runBlocking<Unit> {
        expect(1)
        val single = rxSingle(coroutineContext) {
            expect(4)
            yield() // back to main, will get cancelled
            expectUnreached()
        }
        expect(2)
        // nothing is called on a disposed rx2 single
        val sub = single.subscribe({
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
    fun testSingleNoWait() {
        val single = rxSingle(DefaultDispatcher) {
            "OK"
        }

        checkSingleValue(single) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testSingleAwait() = runBlocking {
        assertEquals("OK", Single.just("O").await() + "K")
    }

    @Test
    fun testSingleEmitAndAwait() {
        val single = rxSingle(DefaultDispatcher) {
            Single.just("O").await() + "K"
        }

        checkSingleValue(single) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testSingleWithDelay() {
        val single = rxSingle(DefaultDispatcher) {
            Observable.timer(50, TimeUnit.MILLISECONDS).map { "O" }.awaitSingle() + "K"
        }

        checkSingleValue(single) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testSingleException() {
        val single = rxSingle(DefaultDispatcher) {
            Observable.just("O", "K").awaitSingle() + "K"
        }

        checkErroneous(single) {
            assert(it is IllegalArgumentException)
        }
    }

    @Test
    fun testAwaitFirst() {
        val single = rxSingle(DefaultDispatcher) {
            Observable.just("O", "#").awaitFirst() + "K"
        }

        checkSingleValue(single) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testAwaitLast() {
        val single = rxSingle(DefaultDispatcher) {
            Observable.just("#", "O").awaitLast() + "K"
        }

        checkSingleValue(single) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testExceptionFromObservable() {
        val single = rxSingle(DefaultDispatcher) {
            try {
                Observable.error<String>(RuntimeException("O")).awaitFirst()
            } catch (e: RuntimeException) {
                Observable.just(e.message!!).awaitLast() + "K"
            }
        }

        checkSingleValue(single) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testExceptionFromCoroutine() {
        val single = rxSingle<String>(DefaultDispatcher) {
            throw IllegalStateException(Observable.just("O").awaitSingle() + "K")
        }

        checkErroneous(single) {
            assert(it is IllegalStateException)
            assertEquals("OK", it.message)
        }
    }
}
