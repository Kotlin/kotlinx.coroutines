package kotlinx.coroutines.channels

import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.testing.TestBase
import kotlinx.coroutines.testing.TestResult

open class ChannelTestBase : TestBase() {
    fun TestChannelKind.Companion.runTestForEach(
        testBody: suspend CoroutineScope.(TestChannelKind) -> Unit
    ): TestResult = runTest {
        TestChannelKind.entries.forEach { kind ->
            testBody(kind)
        }
    }

    fun runTestForEach(
        testBody: suspend CoroutineScope.(TestChannelKind) -> Unit
    ): TestResult = TestChannelKind.runTestForEach(testBody)
}
