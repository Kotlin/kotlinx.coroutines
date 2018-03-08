package kotlinx.coroutines.experimental.channels

import kotlinx.coroutines.experimental.CoroutineStart
import kotlinx.coroutines.experimental.TestBase
import kotlinx.coroutines.experimental.Unconfined
import kotlinx.coroutines.experimental.launch
import kotlin.coroutines.experimental.coroutineContext
import kotlin.test.Test

class SubscribableValueTest : TestBase() {

    @Test
    fun testBasicScenario() = runTest {
        expect(1)
        val subscribable = SubscribableValue(42)
        val variable by subscribable
        check(subscribable.value == 42)
        check(variable == 42)
        launch(coroutineContext, start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            val sub = subscribable.openSubscription()
            check(sub.receive() == 42)
            expect(3)
            try {
                sub.receive()
                expectUnreached()
            } catch (e: ClosedReceiveChannelException) {
                // expected exception
            }
            expect(4)
        }
        finish(5)
    }

    @Test
    fun testOpenSubscriptionAlwaysStartByTheCurrentValue() {
        expect(1)
        val subscribable = SubscribableValue(42)
        launch(Unconfined) {
            expect(2)
            check(subscribable.openSubscription().first() == 42)
            check(subscribable.openSubscription().first() == 42)
            expect(3)
        }
        finish(4)
    }

    @Test
    fun testObservableValue() {
        expect(1)
        val subscribable = SubscribableValue(42)
        val value by subscribable
        check(subscribable.value == 42)
        check(value == 42)
        launch(Unconfined) {
            expect(2)
            check(subscribable.openSubscription().first() == 42)
            check(subscribable.openSubscription().first() == 42)
            expect(3)
        }
        finish(4)
    }
}
