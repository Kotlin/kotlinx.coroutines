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

package kotlinx.coroutines.experimental.rx1

import kotlinx.coroutines.experimental.*
import org.hamcrest.core.IsEqual
import org.hamcrest.core.IsInstanceOf
import org.hamcrest.core.IsNull
import org.junit.Assert.*
import org.junit.Test
import rx.Observable
import rx.Single
import java.util.concurrent.TimeUnit

/**
 * Tests emitting single item with [rxSingle].
 */
class SingleTest : TestBase() {
    @Test
    fun testBasicSuccess() = runBlocking<Unit> {
        expect(1)
        val single = rxSingle(context) {
            expect(4)
            "OK"
        }
        expect(2)
        single.subscribe { value ->
            expect(5)
            assertThat(value, IsEqual("OK"))
        }
        expect(3)
        yield() // to started coroutine
        finish(6)
    }

    @Test
    fun testBasicFailure() = runBlocking<Unit> {
        expect(1)
        val single = rxSingle(context) {
            expect(4)
            throw RuntimeException("OK")
        }
        expect(2)
        single.subscribe({
            expectUnreached()
        }, { error ->
            expect(5)
            assertThat(error, IsInstanceOf(RuntimeException::class.java))
            assertThat(error.message, IsEqual("OK"))
        })
        expect(3)
        yield() // to started coroutine
        finish(6)
    }


    @Test
    fun testBasicUnsubscribe() = runBlocking<Unit> {
        expect(1)
        val single = rxSingle(context) {
            expect(4)
            yield() // back to main, will get cancelled
            expectUnreached()
        }
        expect(2)
        val sub = single.subscribe({
            expectUnreached()
        }, { error ->
            expect(6)
            assertThat(error, IsInstanceOf(CancellationException::class.java))
        })
        expect(3)
        yield() // to started coroutine
        expect(5)
        sub.unsubscribe() // will cancel coroutine
        yield()
        finish(7)
    }

    @Test
    fun testSingleNoWait() {
        val single = rxSingle(CommonPool) {
            "OK"
        }

        checkSingleValue(single) {
            assertThat(it, IsEqual("OK"))
        }
    }

    @Test
    fun testSingleNullNoWait() {
        val single = rxSingle<String?>(CommonPool) {
            null
        }

        checkSingleValue(single) {
            assertThat(it, IsNull())
        }
    }

    @Test
    fun testSingleAwait() = runBlocking {
        assertEquals("OK", Single.just("O").await() + "K")
    }

    @Test
    fun testSingleEmitAndAwait() {
        val single = rxSingle(CommonPool) {
            Single.just("O").await() + "K"
        }

        checkSingleValue(single) {
            assertThat(it, IsEqual("OK"))
        }
    }

    @Test
    fun testSingleWithDelay() {
        val single = rxSingle(CommonPool) {
            Observable.timer(50, TimeUnit.MILLISECONDS).map { "O" }.awaitSingle() + "K"
        }

        checkSingleValue(single) {
            assertThat(it, IsEqual("OK"))
        }
    }

    @Test
    fun testSingleException() {
        val single = rxSingle(CommonPool) {
            Observable.just("O", "K").awaitSingle() + "K"
        }

        checkErroneous(single) {
            assertThat(it, IsInstanceOf(IllegalArgumentException::class.java))
        }
    }

    @Test
    fun testAwaitFirst() {
        val single = rxSingle(CommonPool) {
            Observable.just("O", "#").awaitFirst() + "K"
        }

        checkSingleValue(single) {
            assertThat(it, IsEqual("OK"))
        }
    }

    @Test
    fun testAwaitLast() {
        val single = rxSingle(CommonPool) {
            Observable.just("#", "O").awaitLast() + "K"
        }

        checkSingleValue(single) {
            assertThat(it, IsEqual("OK"))
        }
    }

    @Test
    fun testExceptionFromObservable() {
        val single = rxSingle(CommonPool) {
            try {
                Observable.error<String>(RuntimeException("O")).awaitFirst()
            } catch (e: RuntimeException) {
                Observable.just(e.message!!).awaitLast() + "K"
            }
        }

        checkSingleValue(single) {
            assertThat(it, IsEqual("OK"))
        }
    }

    @Test
    fun testExceptionFromCoroutine() {
        val single = rxSingle<String>(CommonPool) {
            throw RuntimeException(Observable.just("O").awaitSingle() + "K")
        }

        checkErroneous(single) {
            assertThat(it, IsInstanceOf(RuntimeException::class.java))
            assertEquals("OK", it.message)
        }
    }
}
