package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import kotlin.test.*

class AwaitCancellationTest : TestBase() {

    @Test
    fun testCancellation() = runTest(expected = { it is CancellationException }) {
        expect(1)
        coroutineScope {
            val deferred: Deferred<Nothing> = async {
                expect(2)
                awaitCancellation()
            }
            yield()
            expect(3)
            require(deferred.isActive)
            deferred.cancel()
            finish(4)
            deferred.await()
        }
    }
}
