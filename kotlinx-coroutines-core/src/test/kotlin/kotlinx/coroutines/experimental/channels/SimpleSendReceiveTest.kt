package kotlinx.coroutines.experimental.channels

import kotlinx.coroutines.experimental.CommonPool
import kotlinx.coroutines.experimental.launch
import kotlinx.coroutines.experimental.runBlocking
import org.junit.Test
import org.junit.runner.RunWith
import org.junit.runners.Parameterized
import kotlin.test.assertEquals

@RunWith(Parameterized::class)
class SimpleSendReceiveTest(
    val kind: TestChannelKind,
    val n: Int
) {
    companion object {
        @Parameterized.Parameters(name = "{0}, n={1}")
        @JvmStatic
        fun params(): Collection<Array<Any>> = TestChannelKind.values().flatMap { kind ->
            listOf(0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 100, 1000).map { n ->
                arrayOf<Any>(kind, n)
            }
        }
    }

    val channel = kind.create()

    @Test
    fun testSimpleSendReceive() = runBlocking {
        launch(CommonPool) {
            repeat(n) { channel.send(it) }
            channel.close()
        }
        var received = 0
        for (x in channel) {
            assertEquals(received++, x)
        }
        assertEquals(n, received)
    }
}