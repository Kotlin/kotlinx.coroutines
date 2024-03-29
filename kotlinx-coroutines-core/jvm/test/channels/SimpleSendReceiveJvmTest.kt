package kotlinx.coroutines.channels

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import org.junit.Test
import org.junit.runner.*
import org.junit.runners.*
import kotlin.test.*

@RunWith(Parameterized::class)
class SimpleSendReceiveJvmTest(
    private val kind: TestChannelKind,
    val n: Int,
    val concurrent: Boolean
) : TestBase() {
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

    val channel = kind.create<Int>()

    @Test
    fun testSimpleSendReceive() = runBlocking {
        val ctx = if (concurrent) Dispatchers.Default else coroutineContext
        launch(ctx) {
            repeat(n) { channel.send(it) }
            channel.close()
        }
        var expected = 0
        for (x in channel) {
            if (!kind.isConflated) {
                assertEquals(expected++, x)
            } else {
                assertTrue(x >= expected)
                expected = x + 1
            }
        }
        if (!kind.isConflated) {
            assertEquals(n, expected)
        }
    }
}
