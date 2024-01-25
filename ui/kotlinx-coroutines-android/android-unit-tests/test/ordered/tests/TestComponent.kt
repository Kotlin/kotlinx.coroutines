package ordered.tests

import kotlinx.coroutines.*

public class TestComponent {
    internal lateinit var caughtException: Throwable
    private val scope =
        CoroutineScope(SupervisorJob() + Dispatchers.Main + CoroutineExceptionHandler { _, e -> caughtException = e})
    public var launchCompleted = false
    public var delayedLaunchCompleted = false

    fun launchSomething() {
        scope.launch {
            launchCompleted = true
        }
    }

    fun launchDelayed() {
        scope.launch {
            delay(Long.MAX_VALUE / 2)
            delayedLaunchCompleted = true
        }
    }
}
