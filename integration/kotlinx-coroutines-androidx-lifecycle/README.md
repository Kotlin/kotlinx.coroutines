# Module kotlinx-coroutines-androidx-lifecycle

Integration with AndroidX [Lifecycle](
https://developer.android.com/reference/kotlin/androidx/lifecycle/Lifecycle
) and [LifecycleOwner](
https://developer.android.com/reference/kotlin/androidx/lifecycle/LifecycleOwner
).

Extension properties:

| **Name** | **Description**
| -------- | ---------------
| [Lifecycle.coroutineScope][lifecycleScope] | A scope that dispatches on Android Main thread and is active until the Lifecycle is destroyed.
| [LifecycleOwner.coroutineScope][lifecycleOwnerScope] | A scope that dispatches on Android Main thread and is active until the LifecycleOwner is destroyed.
| [Lifecycle.job][lifecycleJob] | A job that is cancelled when the Lifecycle is destroyed.

Extension functions:

| **Name** | **Description**
| -------- | ---------------
| [Lifecycle.createJob][lifecycleCreateJob] | A job that is active while the state is at least the passed one.
| [Lifecycle.createScope][lifecycleCreateScope] | A scope that dispatches on Android Main thread and is active while the state is at least the passed one.

## Example

```kotlin
class MainActivity : AppCompatActivity() {

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)
        lifecycle.coroutineScope.launch {
            someSuspendFunction()
            someOtherSuspendFunction()
            someCancellableSuspendFunction()
        }
    }
    
    override fun onStart() {
        super.onStart()
        val startedScope = lifecycle.createScope(activeWhile = Lifecycle.State.STARTED)
        startedScope.launch {
            aCancellableSuspendFunction()
            yetAnotherCancellableSuspendFunction()
        }
        startedScope.aMethodThatWillLaunchSomeCoroutines()
    }
}
```

# Package kotlinx.coroutines.androidx.lifecycle

Integration with AndroidX [Lifecycle](https://developer.android.com/reference/kotlin/androidx/lifecycle/Lifecycle)
and [LifecycleOwner](https://developer.android.com/reference/kotlin/androidx/lifecycle/LifecycleOwner).

<!--- MODULE kotlinx-coroutines-core -->
<!--- INDEX kotlinx.coroutines -->
<!--- MODULE kotlinx-coroutines-androidx-lifecycle -->
<!--- INDEX kotlinx.coroutines.androidx.lifecycle -->
<!--- END -->
