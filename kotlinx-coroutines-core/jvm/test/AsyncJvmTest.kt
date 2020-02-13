/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.test.*

class AsyncJvmTest : TestBase() {
    // This must be a common test but it fails on JS because of KT-21961
    @Test
    fun testAsyncWithFinally() = runTest {
         launch(Dispatchers.Default) {

         }

        launch(Dispatchers.IO) {

        }
    }
}
