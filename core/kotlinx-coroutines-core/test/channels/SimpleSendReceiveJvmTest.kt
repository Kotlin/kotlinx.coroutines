/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.channels

import kotlinx.coroutines.experimental.*
import org.hamcrest.core.*
import org.junit.*
import org.junit.Assert.*
import org.junit.runner.*
import org.junit.runners.*
import kotlin.coroutines.experimental.*

@RunWith(Parameterized::class)
class SimpleSendReceiveJvmTest(
    val kind: TestChannelKind,
    val n: Int,
    val concurrent: Boolean
) {
    companion object {
        @Parameterized.Parameters(name = "{0}, n={1}, concurrent={2}")
        @JvmStatic
        fun params(): Collection<Array<Any>> = TestChannelKind.values().flatMap { kind ->
            listOf(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 100, 1000).flatMap { n ->
                listOf(false, true).map { concurrent ->
                    arrayOf<Any>(kind, n, concurrent)
                }
            }
        }
    }

    val channel = kind.create()

    @Test
    fun testSimpleSendReceive() = runBlocking {
        val ctx = if (concurrent) DefaultDispatcher else coroutineContext
        launch(ctx) {
            repeat(n) { channel.send(it) }
            channel.close()
        }
        var expected = 0
        for (x in channel) {
            if (!kind.isConflated) {
                assertThat(x, IsEqual(expected++))
            } else {
                assertTrue(x >= expected)
                expected = x + 1
            }
        }
        if (!kind.isConflated) {
            assertThat(expected, IsEqual(n))
        }
    }
}
