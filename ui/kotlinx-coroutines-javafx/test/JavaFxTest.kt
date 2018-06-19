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

package kotlinx.coroutines.experimental.javafx

import javafx.application.Platform
import kotlinx.coroutines.experimental.*
import org.junit.Before
import org.junit.Test

class JavaFxTest : TestBase() {
    @Before
    fun setup() {
        ignoreLostThreads("JavaFX Application Thread", "Thread-", "QuantumRenderer-")
    }

    @Test
    fun testDelay() {
        try {
            initPlatform()
        } catch (e: UnsupportedOperationException) {
            println("Skipping JavaFxTest in headless environment")
            return // ignore test in headless environments
        }

        runBlocking {
            expect(1)
            val job = launch(JavaFx) {
                check(Platform.isFxApplicationThread())
                expect(2)
                delay(100)
                check(Platform.isFxApplicationThread())
                expect(3)
            }
            job.join()
            finish(4)
        }
    }
}