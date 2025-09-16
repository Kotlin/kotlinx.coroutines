package kotlinx.coroutines.flow

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlin.coroutines.*
import kotlin.test.*
import kotlin.time.Duration
import kotlin.time.Duration.Companion.milliseconds

/**
 * Functional tests for [SharingStarted] using [withVirtualTime] and a DSL to describe
 * testing scenarios and expected behavior for different implementations.
 */
class SharingStartedTest : TestBase() {
    @Test
    fun testEagerly() =
        testSharingStarted(SharingStarted.Eagerly, SharingCommand.START) {
            subscriptions(1)
            rampUpAndDown()
            subscriptions(0)
            delay(100)
        }

    @Test
    fun testLazily() =
        testSharingStarted(SharingStarted.Lazily) {
            subscriptions(1, SharingCommand.START)
            rampUpAndDown()
            subscriptions(0)
        }

    @Test
    fun testWhileSubscribed() =
        testSharingStarted(SharingStarted.WhileSubscribed()) {
            subscriptions(1, SharingCommand.START)
            rampUpAndDown()
            subscriptions(0, SharingCommand.STOP)
            delay(100)
        }

    @Test
    fun testWhileSubscribedExpireImmediately() =
        testSharingStarted(SharingStarted.WhileSubscribed(replayExpirationMillis = 0)) {
            subscriptions(1, SharingCommand.START)
            rampUpAndDown()
            subscriptions(0, SharingCommand.STOP_AND_RESET_REPLAY_CACHE)
            delay(100)
        }

    @Test
    fun testWhileSubscribedWithTimeout() =
        testSharingStarted(SharingStarted.WhileSubscribed(stopTimeoutMillis = 100)) {
            subscriptions(1, SharingCommand.START)
            rampUpAndDown()
            subscriptions(0)
            delay(50) // don't give it time to stop
            subscriptions(1) // resubscribe again
            rampUpAndDown()
            subscriptions(0)
            afterTime(100.milliseconds, SharingCommand.STOP)
            delay(100)
        }

    @Test
    fun testWhileSubscribedExpiration() =
        testSharingStarted(SharingStarted.WhileSubscribed(replayExpirationMillis = 200)) {
            subscriptions(1, SharingCommand.START)
            rampUpAndDown()
            subscriptions(0, SharingCommand.STOP)
            delay(150) // don't give it time to reset cache
            subscriptions(1, SharingCommand.START)
            rampUpAndDown()
            subscriptions(0, SharingCommand.STOP)
            afterTime(200.milliseconds, SharingCommand.STOP_AND_RESET_REPLAY_CACHE)
        }

    @Test
    fun testWhileSubscribedStopAndExpiration() =
        testSharingStarted(SharingStarted.WhileSubscribed(stopTimeoutMillis = 400, replayExpirationMillis = 300)) {
            subscriptions(1, SharingCommand.START)
            rampUpAndDown()
            subscriptions(0)
            delay(350) // don't give it time to stop
            subscriptions(1)
            rampUpAndDown()
            subscriptions(0)
            afterTime(400.milliseconds, SharingCommand.STOP)
            delay(250) // don't give it time to reset cache
            subscriptions(1, SharingCommand.START)
            rampUpAndDown()
            subscriptions(0)
            afterTime(400.milliseconds, SharingCommand.STOP)
            afterTime(300.milliseconds, SharingCommand.STOP_AND_RESET_REPLAY_CACHE)
            delay(100)
        }

    private suspend fun SharingStartedDsl.rampUpAndDown() {
        for (i in 2..10) {
            delay(100)
            subscriptions(i)
        }
        delay(1000)
        for (i in 9 downTo 1) {
            subscriptions(i)
            delay(100)
        }
    }

    private fun testSharingStarted(
        started: SharingStarted,
        initialCommand: SharingCommand? = null,
        scenario: suspend SharingStartedDsl.() -> Unit
    ) = withVirtualTime {
        expect(1)
        val dsl = SharingStartedDsl(started, initialCommand, coroutineContext)
        dsl.launch()
        // repeat every scenario 3 times
        repeat(3) {
            dsl.scenario()
            delay(1000)
        }
        dsl.stop()
        finish(2)
    }

    private class SharingStartedDsl(
        val started: SharingStarted,
        initialCommand: SharingCommand?,
        coroutineContext: CoroutineContext
    ) {
        val subscriptionCount = MutableStateFlow(0)
        var previousCommand: SharingCommand? = null
        var expectedCommand: SharingCommand? = initialCommand
        val dispatcher = coroutineContext[ContinuationInterceptor] as VirtualTimeDispatcher
        var expectedTime = dispatcher.currentTime
        val scope = CoroutineScope(coroutineContext + Job())

        suspend fun launch() {
            started
                .command(subscriptionCount.asStateFlow())
                .onEach { checkCommand(it) }
                .launchIn(scope)
            letItRun()
        }

        fun checkCommand(command: SharingCommand) {
            assertTrue(command != previousCommand)
            previousCommand = command
            assertEquals(expectedCommand, command)
            assertEquals(expectedTime, dispatcher.currentTime)
        }

        suspend fun subscriptions(count: Int, command: SharingCommand? = null) {
            expectedTime = dispatcher.currentTime
            subscriptionCount.value = count
            if (command != null) {
                afterTime(Duration.ZERO, command)
            } else {
                letItRun()
            }
        }

        suspend fun afterTime(time: Duration, command: SharingCommand) {
            expectedCommand = command
            val remaining = (time - 1.milliseconds).coerceAtLeast(Duration.ZERO) // previous letItRun delayed 1ms
            expectedTime += remaining
            delay(remaining)
            letItRun()
        }

        private suspend fun letItRun() {
            delay(1.milliseconds)
            assertEquals(expectedCommand, previousCommand) // make sure expected command was emitted
            expectedTime += 1.milliseconds // make one more time tick we've delayed
        }

        fun stop() {
            scope.cancel()
        }
    }
}
