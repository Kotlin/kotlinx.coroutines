package kotlinx.coroutines

import kotlinx.coroutines.testing.*
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
