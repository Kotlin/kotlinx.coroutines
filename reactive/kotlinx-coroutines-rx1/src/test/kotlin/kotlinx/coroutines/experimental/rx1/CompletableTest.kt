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
import org.hamcrest.core.*
import org.junit.*
import org.junit.Assert.*
import kotlin.coroutines.experimental.*

class CompletableTest : TestBase() {
    @Test
    fun testBasicSuccess() = runBlocking<Unit> {
        expect(1)
        val completable = rxCompletable(coroutineContext) {
            expect(4)
        }
        expect(2)
        completable.subscribe {
            expect(5)
        }
        expect(3)
        yield() // to completable coroutine
        finish(6)
    }

    @Test
    fun testBasicFailure() = runBlocking<Unit> {
        expect(1)
        val completable = rxCompletable(coroutineContext) {
            expect(4)
            throw RuntimeException("OK")
        }
        expect(2)
        completable.subscribe({
            expectUnreached()
        }, { error ->
            expect(5)
            assertThat(error, IsInstanceOf(RuntimeException::class.java))
            assertThat(error.message, IsEqual("OK"))
        })
        expect(3)
        yield() // to completable coroutine
        finish(6)
    }

    @Test
    fun testBasicUnsubscribe() = runBlocking<Unit> {
        expect(1)
        val completable = rxCompletable(coroutineContext) {
            expect(4)
            yield() // back to main, will get cancelled
            expectUnreached()
        }
        expect(2)
        val sub = completable.subscribe({
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
    fun testAwaitSuccess() = runBlocking<Unit> {
        expect(1)
        val completable = rxCompletable(coroutineContext) {
            expect(3)
        }
        expect(2)
        completable.awaitCompleted() // shall launch coroutine
        finish(4)
    }

    @Test
    fun testAwaitFailure() = runBlocking<Unit> {
        expect(1)
        val completable = rxCompletable(coroutineContext) {
            expect(3)
            throw RuntimeException("OK")
        }
        expect(2)
        try {
            completable.awaitCompleted() // shall launch coroutine and throw exception
            expectUnreached()
        } catch (e: RuntimeException) {
            finish(4)
            assertThat(e.message, IsEqual("OK"))
        }
    }
}
