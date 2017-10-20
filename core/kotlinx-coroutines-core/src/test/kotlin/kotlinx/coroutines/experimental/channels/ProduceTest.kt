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

package kotlinx.coroutines.experimental.channels

import kotlinx.coroutines.experimental.Job
import kotlinx.coroutines.experimental.JobCancellationException
import kotlinx.coroutines.experimental.TestBase
import org.junit.Test

class ProduceTest : TestBase() {
    @Test
    fun testBasic() = runTest {
        val c = produce(coroutineContext) {
            expect(2)
            send(1)
            expect(3)
            send(2)
            expect(6)
        }
        expect(1)
        check(c.receive() == 1)
        expect(4)
        check(c.receive() == 2)
        expect(5)
        check(c.receiveOrNull() == null)
        finish(7)
    }

    @Test
    fun testCancel() = runTest {
        val c = produce(coroutineContext) {
            expect(2)
            send(1)
            expect(3)
            try {
                send(2) // will get cancelled
            } catch (e: Throwable) {
                expect(6)
                check(e is JobCancellationException && e.job == coroutineContext[Job])
                throw e
            }
            expectUnreached()
        }
        expect(1)
        check(c.receive() == 1)
        expect(4)
        c.cancel()
        expect(5)
        check(c.receiveOrNull() == null)
        finish(7)
    }
}