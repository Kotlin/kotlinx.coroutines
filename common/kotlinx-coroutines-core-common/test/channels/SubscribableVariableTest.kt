package kotlinx.coroutines.experimental.channels

import kotlinx.coroutines.experimental.CoroutineStart
import kotlinx.coroutines.experimental.TestBase
import kotlinx.coroutines.experimental.Unconfined
import kotlinx.coroutines.experimental.launch
import kotlinx.coroutines.experimental.yield
import kotlin.coroutines.experimental.coroutineContext
import kotlin.test.Test

class SubscribableVariableTest : TestBase() {

    @kotlin.test.Test
    fun testBasicScenario() = runTest {
        expect(1)
        val subscribable = SubscribableVariable(42)
        var variable by subscribable
        check(subscribable.value == 42)
        check(variable == 42)
        launch(coroutineContext, start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            val sub = subscribable.openSubscription()
            check(sub.receive() == 42)
            expect(3)
            check(sub.receive() == 24) // suspends
            expect(6)
        }
        expect(4)
        variable = 24
        check(subscribable.value == 24)
        check(variable == 24)
        expect(5)
        yield() // to child
        finish(7)
    }

    @Test
    fun testOpenSubscriptionAlwaysStartByTheCurrentValue() {
        expect(1)
        val subscribable = SubscribableVariable(42)
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
