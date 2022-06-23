/*
 * Copyright 2016-2022 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import org.junit.*
import java.io.*


@Suppress("BlockingMethodInNonBlockingContext")
class JobCancellationExceptionSerializerTest : TestBase() {

    @Test
    fun testSerialization() = runTest {
        try {
            coroutineScope {
                expect(1)

                launch {
                    expect(2)
                    try {
                        hang {}
                    } catch (e: CancellationException) {
                        throw RuntimeException("RE2", e)
                    }
                }

                launch {
                    expect(3)
                    throw RuntimeException("RE1")
                }
            }
        } catch (e: Throwable) {
            // Should not fail
            ObjectOutputStream(ByteArrayOutputStream()).use {
                it.writeObject(e)
            }
            finish(4)
        }
    }
}
