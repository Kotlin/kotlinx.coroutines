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

package kotlinx.coroutines.experimental

import org.hamcrest.core.IsEqual
import org.hamcrest.core.IsInstanceOf
import org.hamcrest.core.IsNull
import org.junit.Assert.assertThat
import org.junit.Assert.fail
import org.junit.Test

class CompletableDeferredTest : TestBase() {
    @Test
    fun testFresh() {
        val c = CompletableDeferred<String>()
        checkFresh(c)
    }

    private fun checkFresh(c: CompletableDeferred<String>) {
        assertThat(c.isActive, IsEqual(true))
        assertThat(c.isCancelled, IsEqual(false))
        assertThat(c.isCompleted, IsEqual(false))
        assertThat(c.isCompletedExceptionally, IsEqual(false))
        assertThrows<IllegalStateException> { c.getCancellationException() }
        assertThrows<IllegalStateException> { c.getCompleted() }
        assertThrows<IllegalStateException> { c.getCompletionExceptionOrNull() }
    }

    @Test
    fun testComplete() {
        val c = CompletableDeferred<String>()
        assertThat(c.complete("OK"), IsEqual(true))
        checkCompleteOk(c)
        assertThat(c.complete("OK"), IsEqual(false))
        checkCompleteOk(c)
    }

    private fun checkCompleteOk(c: CompletableDeferred<String>) {
        assertThat(c.isActive, IsEqual(false))
        assertThat(c.isCancelled, IsEqual(false))
        assertThat(c.isCompleted, IsEqual(true))
        assertThat(c.isCompletedExceptionally, IsEqual(false))
        assertThat(c.getCancellationException(), IsInstanceOf(JobCancellationException::class.java))
        assertThat(c.getCompleted(), IsEqual("OK"))
        assertThat(c.getCompletionExceptionOrNull(), IsNull())
    }

    @Test
    fun testCompleteWithException() {
        val c = CompletableDeferred<String>()
        assertThat(c.completeExceptionally(TestException()), IsEqual(true))
        checkCompleteTestException(c)
        assertThat(c.completeExceptionally(TestException()), IsEqual(false))
        checkCompleteTestException(c)
    }

    private fun checkCompleteTestException(c: CompletableDeferred<String>) {
        assertThat(c.isActive, IsEqual(false))
        assertThat(c.isCancelled, IsEqual(false))
        assertThat(c.isCompleted, IsEqual(true))
        assertThat(c.isCompletedExceptionally, IsEqual(true))
        assertThat(c.getCancellationException(), IsInstanceOf(JobCancellationException::class.java))
        assertThrows<TestException> { c.getCompleted() }
        assertThat(c.getCompletionExceptionOrNull(), IsInstanceOf(TestException::class.java))
    }

    @Test
    fun testCancel() {
        val c = CompletableDeferred<String>()
        assertThat(c.cancel(), IsEqual(true))
        checkCancel(c)
        assertThat(c.cancel(), IsEqual(false))
        checkCancel(c)
    }

    private fun checkCancel(c: CompletableDeferred<String>) {
        assertThat(c.isActive, IsEqual(false))
        assertThat(c.isCancelled, IsEqual(true))
        assertThat(c.isCompleted, IsEqual(true))
        assertThat(c.isCompletedExceptionally, IsEqual(true))
        assertThat(c.getCancellationException(), IsInstanceOf(CancellationException::class.java))
        assertThrows<CancellationException> { c.getCompleted() }
        assertThat(c.getCompletionExceptionOrNull(), IsInstanceOf(CancellationException::class.java))
    }

    @Test
    fun testCancelWithException() {
        val c = CompletableDeferred<String>()
        assertThat(c.cancel(TestException()), IsEqual(true))
        checkCancelWithException(c)
        assertThat(c.cancel(TestException()), IsEqual(false))
        checkCancelWithException(c)
    }

    private fun checkCancelWithException(c: CompletableDeferred<String>) {
        assertThat(c.isActive, IsEqual(false))
        assertThat(c.isCancelled, IsEqual(true))
        assertThat(c.isCompleted, IsEqual(true))
        assertThat(c.isCompletedExceptionally, IsEqual(true))
        assertThat(c.getCancellationException(), IsInstanceOf(JobCancellationException::class.java))
        assertThrows<TestException> { c.getCompleted() }
        assertThat(c.getCompletionExceptionOrNull(), IsInstanceOf(TestException::class.java))
    }

    @Test
    fun testParentCancelsChild() {
        val parent = Job()
        val c = CompletableDeferred<String>(parent)
        checkFresh(c)
        parent.cancel()
        assertThat(parent.isActive, IsEqual(false))
        assertThat(parent.isCancelled, IsEqual(true))
        checkCancel(c)
    }

    @Test
    fun testParentActiveOnChildCompletion() {
        val parent = Job()
        val c = CompletableDeferred<String>(parent)
        checkFresh(c)
        assertThat(parent.isActive, IsEqual(true))
        assertThat(c.complete("OK"), IsEqual(true))
        checkCompleteOk(c)
        assertThat(parent.isActive, IsEqual(true))
    }

    @Test
    fun testParentActiveOnChildException() {
        val parent = Job()
        val c = CompletableDeferred<String>(parent)
        checkFresh(c)
        assertThat(parent.isActive, IsEqual(true))
        assertThat(c.completeExceptionally(TestException()), IsEqual(true))
        checkCompleteTestException(c)
        assertThat(parent.isActive, IsEqual(true))
    }

    @Test
    fun testParentActiveOnChildCancellation() {
        val parent = Job()
        val c = CompletableDeferred<String>(parent)
        checkFresh(c)
        assertThat(parent.isActive, IsEqual(true))
        assertThat(c.cancel(), IsEqual(true))
        checkCancel(c)
        assertThat(parent.isActive, IsEqual(true))
    }

    @Test
    fun testAwait() = runBlocking {
        expect(1)
        val c = CompletableDeferred<String>()
        launch(coroutineContext, CoroutineStart.UNDISPATCHED) {
            expect(2)
            assertThat(c.await(), IsEqual("OK")) // suspends
            expect(5)
            assertThat(c.await(), IsEqual("OK")) // does not suspend
            expect(6)
        }
        expect(3)
        c.complete("OK")
        expect(4)
        yield() // to launch
        finish(7)
    }

    private inline fun <reified T: Throwable> assertThrows(block: () -> Unit) {
        try {
            block()
            fail("Should not complete normally")
        } catch (e: Throwable) {
            assertThat(e, IsInstanceOf(T::class.java))
        }
    }

    class TestException : Throwable()
}