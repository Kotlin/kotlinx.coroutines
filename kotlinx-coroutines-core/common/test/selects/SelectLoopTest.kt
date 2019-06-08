/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("NAMED_ARGUMENTS_NOT_ALLOWED") // KT-21913

package kotlinx.coroutines.selects

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlin.test.*

class SelectLoopTest : TestBase() {
    // https://github.com/Kotlin/kotlinx.coroutines/issues/1130
    @Test
    fun testChannelSelectLoop() = runTest(
        expected = { it is TestException }
    ) {
        expect(1)
        val channel = Channel<Unit>()
        val job = launch {
            expect(2)
            channel.send(Unit)
            expect(3)
            throw TestException()
        }
        var isDone = false
        while (!isDone) {
            select<Unit> {
                channel.onReceiveOrNull {
                    expect(4)
                    assertEquals(Unit, it)
                }
                job.onJoin {
                    expect(5)
                    isDone = true
                }
            }
        }
        finish(6)
    }
}