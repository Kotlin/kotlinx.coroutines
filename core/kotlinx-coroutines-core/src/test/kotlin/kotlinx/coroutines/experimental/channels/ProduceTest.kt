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

import kotlinx.coroutines.experimental.TestBase
import kotlinx.coroutines.experimental.runBlocking
import org.junit.Test

class ProduceTest : TestBase() {
    @Test
    fun testBasic() = runBlocking {
        val c = produce(coroutineContext) {
            send(1)
            send(2)
        }
        check(c.receive() == 1)
        check(c.receive() == 2)
        check(c.receiveOrNull() == null)
    }

    @Test
    fun testCancel() = runBlocking {
        val c = produce(coroutineContext) {
            send(1)
            send(2)
            expectUnreached()
        }
        check(c.receive() == 1)
        c.cancel()
        check(c.receiveOrNull() == null)
    }
}