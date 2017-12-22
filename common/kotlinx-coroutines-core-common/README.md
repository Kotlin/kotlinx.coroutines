# Module kotlinx-coroutines-core-js

Common primitives to work with coroutines in
[mutliplatform Kotlin projects](https://kotlinlang.org/docs/reference/multiplatform.html).

Note, that documentation is currently provided in platform-specific modules only:
* [kotlinx-coroutines-core](../../core/kotlinx-coroutines-core/README.md) for Kotlin/JVM.
* [kotlinx-coroutines-core-js](../../js/kotlinx-coroutines-core-js/README.md) for Kotlin/JS.

Coroutine builder functions:

| **Name**      | **Result**    | **Scope**        | **Description**
| ------------- | ------------- | ---------------- | ---------------
| `launch`      | `Job`         | `CoroutineScope` | Launches coroutine that does not have any result 
| `async`       | `Deferred`    | `CoroutineScope` | Returns a single value with the future result
| `runBlocking` | `T`           | `CoroutineScope` | Blocks the event loop while the coroutine runs

Coroutine dispatchers implementing `CoroutineDispatcher`:
 
| **Name**                    | **Description**
| --------------------------- | ---------------
| `DefaultDispatcher`         | Platform-specific default dispatcher
| `Unconfined`                | Does not confine coroutine execution in any way

More context elements:

| **Name**                    | **Description**
| --------------------------- | ---------------
| `NonCancellable`            | A non-cancelable job that is always active
| `CoroutineExceptionHandler` | Handler for uncaught exception

Top-level suspending functions:

| **Name**            | **Description**
| ------------------- | ---------------
| `delay`             | Non-blocking sleep
| `yield`             | Yields thread in single-threaded dispatchers
| `withContext`       | Switches to a different context
| `withTimeout`       | Set execution time-limit with exception on timeout 
| `withTimeoutOrNull` | Set execution time-limit will null result on timeout

Cancellation support for user-defined suspending functions is available with `suspendCancellableCoroutine`
helper function. `NonCancellable` job object is provided to suppress cancellation with 
`run(NonCancellable) {...}` block of code.
