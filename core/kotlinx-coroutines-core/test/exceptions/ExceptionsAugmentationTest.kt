/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.exceptions

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.channels.*
import org.junit.*
import java.util.concurrent.*
import kotlin.coroutines.experimental.*

class ExceptionsAugmentationTest : TestBase() {

    @Test
    fun testAwait() = runTest {
        val deferred = async(coroutineContext) {
            throw ExecutionException(null)
        }

        try {
            deferred.await()
        } catch (e: ExecutionException) {
            e.printStackTrace()
        }
    }

    @Test
    fun testReceiveFromChannel() = runTest {
        val channel = Channel<Int>(1)
        launch(coroutineContext) {
            channel.close(IllegalArgumentException())
        }

        try {
            channel.receive()
            expectUnreached()
        } catch (e: IllegalArgumentException) {
            e.printStackTrace()
        }
    }

    @Test
    fun testReceiveFromClosedChannel() = runTest {
        val channel = Channel<Int>(1)
        channel.close(IllegalArgumentException())

        try {
            channel.receive()
            expectUnreached()
        } catch (e: IllegalArgumentException) {
            e.printStackTrace()
        }
    }
}
