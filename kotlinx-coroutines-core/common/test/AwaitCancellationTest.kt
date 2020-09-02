/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.test.*

class AwaitCancellationTest : TestBase() {

    @Test
    fun testCancellation() = runTest(expected = { it is CancellationException }) {
        expect(1)
        coroutineScope {
            val deferred: Deferred<Nothing> = async {
                expect(2)
                awaitCancellation()
            }
            yield()
            expect(3)
            require(deferred.isActive)
            deferred.cancel()
            finish(4)
            deferred.await()
        }
    }
}
