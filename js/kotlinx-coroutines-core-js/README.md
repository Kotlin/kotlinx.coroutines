# Module kotlinx-coroutines-core-js

Core primitives to work with coroutines on Kotlin/JS.

Coroutine builder functions:

| **Name**      | **Result**    | **Scope**        | **Description**
| ------------- | ------------- | ---------------- | ---------------
| [launch]      | [Job]         | [CoroutineScope] | Launches coroutine that does not have any result 
| [async]       | [Deferred]    | [CoroutineScope] | Returns a single value with the future result
| [runBlocking] | `T`           | [CoroutineScope] | Blocks the event loop while the coroutine runs

Coroutine dispatchers implementing [CoroutineDispatcher]:
 
| **Name**                    | **Description**
| --------------------------- | ---------------
| [DefaultDispatcher]         | Posts execution to JS event loop
| [Unconfined]                | Does not confine coroutine execution in any way

More context elements:

| **Name**                    | **Description**
| --------------------------- | ---------------
| [NonCancellable]            | A non-cancelable job that is always active
| [CoroutineExceptionHandler] | Handler for uncaught exception

Top-level suspending functions:

| **Name**            | **Description**
| ------------------- | ---------------
| [delay]             | Non-blocking sleep
| [yield]             | Yields thread in single-threaded dispatchers
| [withContext]       | Switches to a different context
| [withTimeout]       | Set execution time-limit with exception on timeout 
| [withTimeoutOrNull] | Set execution time-limit will null result on timeout

Cancellation support for user-defined suspending functions is available with [suspendCancellableCoroutine]
helper function. [NonCancellable] job object is provided to suppress cancellation with 
`run(NonCancellable) {...}` block of code.

# Package kotlinx.coroutines.experimental

General-purpose coroutine builders, contexts, and helper functions.

<!--- MODULE kotlinx-coroutines-core-js -->
<!--- INDEX kotlinx.coroutines.experimental -->
[launch]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core-js/kotlinx.coroutines.experimental/launch.html
[Job]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core-js/kotlinx.coroutines.experimental/-job/index.html
[CoroutineScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core-js/kotlinx.coroutines.experimental/-coroutine-scope/index.html
[async]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core-js/kotlinx.coroutines.experimental/async.html
[Deferred]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core-js/kotlinx.coroutines.experimental/-deferred/index.html
[runBlocking]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core-js/kotlinx.coroutines.experimental/run-blocking.html
[CoroutineDispatcher]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core-js/kotlinx.coroutines.experimental/-coroutine-dispatcher/index.html
[DefaultDispatcher]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core-js/kotlinx.coroutines.experimental/-default-dispatcher.html
[Unconfined]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core-js/kotlinx.coroutines.experimental/-unconfined/index.html
[NonCancellable]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core-js/kotlinx.coroutines.experimental/-non-cancellable/index.html
[CoroutineExceptionHandler]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core-js/kotlinx.coroutines.experimental/-coroutine-exception-handler/index.html
[delay]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core-js/kotlinx.coroutines.experimental/delay.html
[yield]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core-js/kotlinx.coroutines.experimental/yield.html
[withContext]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core-js/kotlinx.coroutines.experimental/with-context.html
[withTimeout]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core-js/kotlinx.coroutines.experimental/with-timeout.html
[withTimeoutOrNull]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core-js/kotlinx.coroutines.experimental/with-timeout-or-null.html
[suspendCancellableCoroutine]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core-js/kotlinx.coroutines.experimental/suspend-cancellable-coroutine.html
<!--- END -->
