package kotlinx.coroutines.disambiguation

import kotlinx.coroutines.testing.TestBase
import kotlinx.coroutines.*
import kotlinx.coroutines.timeout.*
import kotlin.test.Test
import kotlin.time.Duration.Companion.seconds

class WithTimeoutAmbiguityTest : TestBase() {

    // The test fails without @LowPriorityInOverloadResolution on the obsolete timeout method
    @Test
    fun testUnambiguousWithStarImports() = runTest {
        expect(1)
        // Use 'withTimeoutOrNull'
        withTimeoutOrNull(100.seconds) {
            expect(2)
            "OK"
        }
        try {
            expect(3)
            withTimeout(1) {
                delay(100.seconds)
            }
            expectUnreached()
        } catch (e: TimeoutException) {
            finish(4)
        }
    }
}
