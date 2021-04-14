/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.test.*

class DispatchersToStringTest {
    @Test
    fun testStrings() {
        assertEquals("Dispatchers.Unconfined", Dispatchers.Unconfined.toString())
        assertEquals("Dispatchers.Default", Dispatchers.Default.toString())
        assertEquals("Dispatchers.IO", Dispatchers.IO.toString())
        assertEquals("Dispatchers.Main[missing]", Dispatchers.Main.toString())
        assertEquals("Dispatchers.Main[missing]", Dispatchers.Main.immediate.toString())
    }
}