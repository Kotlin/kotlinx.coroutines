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

import org.junit.Test
import java.io.IOException
import org.junit.Assert.*

class DeferTest : TestBase() {
    @Test
    fun testSimple(): Unit = runBlocking {
        expect(1)
        val d = defer(context) {
            expect(3)
            42
        }
        expect(2)
        check(d.isActive)
        check(d.await() == 42)
        check(!d.isActive)
        expect(4)
        check(d.await() == 42) // second await -- same result
        finish(5)
    }

    @Test(expected = IOException::class)
    fun testSimpleException(): Unit = runBlocking {
        expect(1)
        val d = defer(context) {
            finish(3)
            throw IOException()
        }
        expect(2)
        d.await() // will throw IOException
    }

    @Test(expected = IOException::class)
    fun testDeferAndYieldException(): Unit = runBlocking {
        expect(1)
        val d = defer(context) {
            expect(3)
            yield() // no effect, parent waiting
            finish(4)
            throw IOException()
        }
        expect(2)
        d.await() // will throw IOException
    }

    @Test
    fun testDeferWithTwoWaiters() = runBlocking {
        expect(1)
        val d = defer(context) {
            expect(5)
            yield()
            expect(9)
            42
        }
        expect(2)
        launch(context) {
            expect(6)
            check(d.await() == 42)
            expect(11)
        }
        expect(3)
        launch(context) {
            expect(7)
            check(d.await() == 42)
            expect(12)
        }
        expect(4)
        yield() // this actually yields control to defer, which produces results and resumes both waiters (in order)
        expect(8)
        yield() // yield again to "d", which completes
        expect(10)
        yield() // yield to both waiters
        finish(13)
    }

    class BadClass {
        override fun equals(other: Any?): Boolean = error("equals")
        override fun hashCode(): Int = error("hashCode")
        override fun toString(): String = error("toString")
    }

    @Test
    fun testDeferBadClass() = runBlocking {
        val bad = BadClass()
        val d = defer(context) {
            expect(1)
            bad
        }
        assertTrue(d.await() === bad)
        finish(2)
    }
}