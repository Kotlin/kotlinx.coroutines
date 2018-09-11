/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.rx1

import kotlinx.coroutines.experimental.*
import org.hamcrest.core.*
import org.junit.*
import org.junit.Assert.*

class CompletableTest : TestBase() {
    @Test
    fun testBasicSuccess() = runBlocking {
        expect(1)
        val completable = rxCompletable {
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
    fun testBasicFailure() = runBlocking {
        expect(1)
        val completable = rxCompletable {
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
    fun testBasicUnsubscribe() = runBlocking {
        expect(1)
        val completable = rxCompletable {
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
    fun testAwaitSuccess() = runBlocking {
        expect(1)
        val completable = rxCompletable {
            expect(3)
        }
        expect(2)
        completable.awaitCompleted() // shall launch coroutine
        finish(4)
    }

    @Test
    fun testAwaitFailure() = runBlocking {
        expect(1)
        val completable = rxCompletable {
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
