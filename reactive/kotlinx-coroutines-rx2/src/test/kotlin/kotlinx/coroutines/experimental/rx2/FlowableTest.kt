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

import kotlinx.coroutines.experimental.*
import org.hamcrest.core.*
import org.junit.*
import kotlin.coroutines.experimental.*

class FlowableTest : TestBase() {
    @Test
    fun testBasicSuccess() = runBlocking<Unit> {
        expect(1)
        val observable = rxFlowable(coroutineContext) {
            expect(4)
            send("OK")
        }
        expect(2)
        observable.subscribe { value ->
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
        val observable = rxFlowable<String>(coroutineContext) {
            expect(4)
            throw RuntimeException("OK")
        }
        expect(2)
        observable.subscribe({
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
        val observable = rxFlowable<String>(coroutineContext) {
            expect(4)
            yield() // back to main, will get cancelled
            expectUnreached()
        }
        expect(2)
        val sub = observable.subscribe({
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
}