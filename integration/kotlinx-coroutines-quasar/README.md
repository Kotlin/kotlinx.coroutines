# Module kotlinx-coroutines-quasar

Integration with [Quasar](http://docs.paralleluniverse.co/quasar/).
It supports invoking Quasar-instrumented suspendable code from within Kotlin
coroutines via [runSuspendable] and invoking Kotlin suspending code from 
Quasar-instrumented code via [runFiberBlocking].

## Example

Invoke Quasar-instrumented suspendable code from Kotlin coroutine via [runSuspendable]:

```kotlin
runSuspendable(SuspendableCallable {
    // Your suspendable code that will be instrumented by Quasar here
})
```

Invoke Kotlin suspending function from Quasar-instrumented suspendable code via [runFiberBlocking]:

```kotlin
runFiberBlocking {
    // Your Kotlin suspending code here
}
```

# Package kotlinx.coroutines.quasar

Integration with [Quasar](http://docs.paralleluniverse.co/quasar/).

<!--- MODULE kotlinx-coroutines-core -->
<!--- INDEX kotlinx.coroutines -->
<!--- MODULE kotlinx-coroutines-quasar -->
<!--- INDEX kotlinx.coroutines.quasar -->
[runSuspendable]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-quasar/kotlinx.coroutines.quasar/run-suspendable.html
[runFiberBlocking]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-quasar/kotlinx.coroutines.quasar/run-fiber-blocking.html
<!--- END -->
