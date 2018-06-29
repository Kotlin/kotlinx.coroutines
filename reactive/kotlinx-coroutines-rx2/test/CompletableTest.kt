/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.rx2

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
        // nothing is called on a disposed rx2 completable
        val sub = completable.subscribe({
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
    fun testAwaitSuccess() = runBlocking<Unit> {
        expect(1)
        val completable = rxCompletable(coroutineContext) {
            expect(3)
        }
        expect(2)
        completable.await() // shall launch coroutine
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
            completable.await() // shall launch coroutine and throw exception
            expectUnreached()
        } catch (e: RuntimeException) {
            finish(4)
            assertThat(e.message, IsEqual("OK"))
        }
    }
}
