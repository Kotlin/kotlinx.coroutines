/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.android

import android.os.*
import kotlinx.coroutines.*
import org.junit.*
import org.junit.runner.*
import org.robolectric.*
import org.robolectric.annotation.*

@RunWith(RobolectricTestRunner::class)
@Config(manifest = Config.NONE, sdk = [28])
class DisabledHandlerTest : TestBase() {

    private var delegateToSuper = false
    private val disabledDispatcher = object : Handler() {
        override fun sendMessageAtTime(msg: Message?, uptimeMillis: Long): Boolean {
            if (delegateToSuper) return super.sendMessageAtTime(msg, uptimeMillis)
            return false
        }
    }.asCoroutineDispatcher()

    @Test
    fun testRunBlocking() {
        expect(1)
        try {
            runBlocking(disabledDispatcher) {
                expectUnreached()
            }
            expectUnreached()
        } catch (e: CancellationException) {
            finish(2)
        }
    }

    @Test
    fun testInvokeOnCancellation() = runTest {
        val job = launch(disabledDispatcher, start = CoroutineStart.LAZY) { expectUnreached() }
        job.invokeOnCompletion { if (it != null) expect(2) }
        yield()
        expect(1)
        job.join()
        finish(3)
    }

    @Test
    fun testWithTimeout() = runTest {
        delegateToSuper = true
        try {
            withContext(disabledDispatcher) {
                expect(1)
                delegateToSuper = false
                delay(Long.MAX_VALUE - 1)
                expectUnreached()
            }
            expectUnreached()
        } catch (e: CancellationException) {
            finish(2)
        }
    }
}
