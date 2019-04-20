package kotlinx.coroutines.test

import kotlinx.coroutines.CoroutineScope
import org.junit.Assert
import java.time.Instant

const val SLOW = 10_000L

/**
 * Assert a block completes within a second or fail the suite
 */
suspend fun CoroutineScope.assertRunsFast(block: suspend CoroutineScope.() -> Unit) {
    val start = Instant.now().toEpochMilli()
    // don''t need to be fancy with timeouts here since anything longer than a few ms is an error
    this.block()
    val duration = Instant.now().minusMillis(start).toEpochMilli()
    Assert.assertTrue("All tests must complete within 2000ms (use longer timeouts to cause failure)", duration < 2_000)
}
