/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental

import kotlin.test.*

class WithContextCommonPoolTest : TestBase() {
    @Test
    fun testCommonPoolNoSuspend() = runTest {
        expect(1)
        val result = withContext(CommonPool) {
            expect(2)
            "OK"
        }
        assertEquals("OK", result)
        finish(3)
    }

    @Test
    fun testCommonPoolWithSuspend() = runTest {
        expect(1)
        val result = withContext(CommonPool) {
            expect(2)
            delay(100)
            expect(3)
            "OK"
        }
        assertEquals("OK", result)
        finish(4)
    }
}