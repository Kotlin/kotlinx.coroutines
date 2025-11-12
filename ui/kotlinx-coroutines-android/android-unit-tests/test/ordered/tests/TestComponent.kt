package ordered.tests

import kotlinx.coroutines.*

class TestComponent {
    internal lateinit var caughtException: Throwable
    private val scope =
        CoroutineScope(SupervisorJob() + Dispatchers.Main + CoroutineExceptionHandler { _, e -> caughtException = e})
    var launchCompleted = false
    var delayedLaunchCompleted = false

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
