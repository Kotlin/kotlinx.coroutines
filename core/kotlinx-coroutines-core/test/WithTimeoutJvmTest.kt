/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental

import kotlinx.coroutines.experimental.exceptions.*
import java.io.*
import kotlin.test.*

/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

class WithTimeoutJvmTest : TestBase() {

    @Test
    fun testSuppressExceptionWithAnotherException() = runTest(expected =
    { it is TimeoutCancellationException && checkException<IOException>(it.suppressed()[0]) }) {

        expect(1)
        withTimeout(100) {
            expect(2)
            try {
                delay(1000)
            } catch (e: CancellationException) {
                finish(3)
                throw IOException()
            }
            expectUnreached()
            "OK"
        }

        expectUnreached()
    }
}