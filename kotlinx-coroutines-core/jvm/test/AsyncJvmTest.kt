/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.test.*


class AsyncJvmTest : TestBase() {
    // We have the same test in common module, but the maintainer uses this particular file
    // and semi-automatically types cmd+N + AsyncJvm in order to duck-tape any JVM samples/repros,
    // please do not remove this test

    @Test
    fun testAsyncWithFinally() = runTest {
        expect(1)

        @Suppress("UNREACHABLE_CODE")
        val d = async {
            expect(3)
            try {
                yield() // to main, will cancel
            } finally {
                expect(6) // will go there on await
                return@async "Fail" // result will not override cancellation
            }
            expectUnreached()
            "Fail2"
        }
        expect(2)
        yield() // to async
        expect(4)
        check(d.isActive && !d.isCompleted && !d.isCancelled)
        d.cancel()
        check(!d.isActive && !d.isCompleted && d.isCancelled)
        check(!d.isActive && !d.isCompleted && d.isCancelled)
        expect(5)
        try {
            d.await() // awaits
            expectUnreached() // does not complete normally
        } catch (e: Throwable) {
            expect(7)
            check(e is CancellationException)
        }
        check(!d.isActive && d.isCompleted && d.isCancelled)
        finish(8)
    }
}
