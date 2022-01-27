/*
 * Copyright 2016-2022 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.android

import kotlinx.coroutines.*
import org.junit.Test
import org.junit.runner.*
import org.robolectric.*
import org.robolectric.annotation.*
import kotlin.test.*

@RunWith(RobolectricTestRunner::class)
@Config(manifest = Config.NONE, sdk = [27])
class AndroidExceptionPreHandlerTest : TestBase() {
    @Test
    fun testUnhandledException() = runTest {
        val previousHandler = Thread.getDefaultUncaughtExceptionHandler()
        try {
            Thread.setDefaultUncaughtExceptionHandler { _, e ->
                expect(3)
                assertIs<TestException>(e)
            }
            expect(1)
            GlobalScope.launch(Dispatchers.Main) {
                expect(2)
                throw TestException()
            }.join()
            finish(4)
        } finally {
            Thread.setDefaultUncaughtExceptionHandler(previousHandler)
        }
    }
}
