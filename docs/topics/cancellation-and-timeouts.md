<contribute-url>https://github.com/Kotlin/kotlinx.coroutines/edit/master/docs/topics/</contribute-url>

[//]: # (title: Cancellation and timeouts)

Cancellation lets you request to stop a coroutine before it completes.
It stops work that's no longer needed, such as when a user closes a window or navigates away in a user interface while a coroutine is still running.
You can use it to release resources early and to stop a coroutine from accessing objects past their disposal.
You can also use cancellation to stop long-running coroutines, for example, sending heartbeats, running scheduled tasks, updating a state to reflect the newest reading (like the clock UI), etc.

Cancellation works through the [`Job`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-job/) handle, which represents the lifecycle of a coroutine and its parent-child relationships.
`Job` allows you to check whether the coroutine is active and allows you to cancel it, along with its children, as defined by [structured concurrency](coroutines-basics.md#coroutine-scope-and-structured-concurrency).

## Cancel coroutines

A coroutine is canceled when the [`cancel()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-job/cancel.html) function is invoked on its `Job` handle.
[Coroutine builder functions](coroutines-basics.md#coroutine-builder-functions) such as
[`.launch()`](coroutines-basics.md#coroutinescope-launch) return a `Job`. The [`.async()`](coroutines-basics.md#coroutinescope-async)
function returns a [`Deferred`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-deferred/), which
implements `Job` and supports the same cancellation behavior.

You can call the `cancel()` function manually, or it can be invoked automatically through cancellation propagation when a parent coroutine is canceled.

When a coroutine is canceled, it throws a [`CancellationException`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-cancellation-exception/) the next time it checks for cancellation.
The [Suspension points and cancellation](#suspension-points-and-cancellation) section covers precisely when this happens, but for now it is enough to know that all suspend functions in the `kotlinx.coroutines` library, such as `delay()` and `awaitCancellation()` explained below, check for cancellation if they suspend.

[`awaitCancellation()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/await-cancellation.html) function suspends a coroutine until it's canceled. It is equivalent to `delay(Duration.INFINITE)`.

Here's an example on how to manually cancel a coroutine:

```kotlin
import kotlinx.coroutines.*
import kotlin.time.Duration

//sampleStart
suspend fun main() {
    withContext(Dispatchers.Default) {
        // Used as a signal that the coroutine has started running
        val started = CompletableDeferred<Unit>()
        
        val job: Job = launch {
            println("The coroutine has started")

            // Completes the CompletableDeferred,
            // signaling that the coroutine has started running
            started.complete(Unit)
            try {
                // Suspends indefinitely
                // This call will never return unless the coroutine is canceled
                awaitCancellation()
            } catch (e: CancellationException) {
                println("The coroutine was canceled: $e")
              
                // Always rethrow cancellation exceptions!
                throw e
            }
            println("This line will never be executed")
        }
      
        // Waits for the coroutine to start before canceling it
        started.await()

        // Cancels the coroutine,
        // so awaitCancellation() throws a CancellationException
        job.cancel()
    }
    // Coroutine builders such as withContext() or coroutineScope()
    // wait for all child coroutines to complete,
    // even when the children are canceled
    println("All coroutines have completed")
}
//sampleEnd
```
{kotlin-runnable="true" id="manual-cancellation-example"}

In this example, [`CompletableDeferred`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-completable-deferred/) is used as a signal that the coroutine has started running.
The coroutine calls `complete()` when it starts executing, and `await()` only returns once that `CompletableDeferred` is completed. This way, cancellation happens only after the coroutine has started running. Without this check, the coroutine could be canceled before it runs the code inside its block. You don't need to have this check to cancel a coroutine, but it is included here to have a consistent example which always prints the explanation lines.

Similarly, a coroutine created by `async` can be canceled, `val deferred = async { ... }`, `deferred.cancel()`. The `async` builder returns a `Deferred` handle, which inherits from `Job`. Hence, the cancellation works in exactly the same way for `Deferred` as it does for `Job`.

> Catching `CancellationException` can break the cancellation propagation.
> If you must catch it, rethrow it to let the cancellation propagate correctly through the coroutine hierarchy.
>
> For more information, see [Coroutine exceptions handling](exception-handling.md#cancellation-and-exceptions).
>
{style="warning"}

### Cancellation propagation

[Structured concurrency](coroutines-basics.md#coroutine-scope-and-structured-concurrency) ensures that canceling a coroutine also cancels all of its children.
This prevents child coroutines from working after the parent has been requested to stop.

Here's an example:

```kotlin
import kotlinx.coroutines.*
import kotlin.time.Duration

//sampleStart
suspend fun main() {
    withContext(Dispatchers.Default) {
        // Used as a signal that the child coroutines have been launched
        val childrenLaunched = CompletableDeferred<Unit>()

        // Launches two child coroutines
        val parentJob = launch {
            launch {
                println("Child coroutine 1 has started running")
                try {
                    awaitCancellation()
                } finally {
                    println("Child coroutine 1 has been canceled")
                }
            }
            launch {
                println("Child coroutine 2 has started running")
                try {
                    awaitCancellation()
                } finally {
                    println("Child coroutine 2 has been canceled")
                }
            }
            // Completes the CompletableDeferred,
            // signaling that the child coroutines have been launched
            childrenLaunched.complete(Unit)
        }
        // Waits for the parent coroutine to signal that it has launched
        // all of its children
        childrenLaunched.await()

        // Cancels the parent coroutine, which cancels all its children
        parentJob.cancel()
    }
}
//sampleEnd
```
{kotlin-runnable="true" id="cancellation-propagation-example"}

In this example, each child coroutine uses a [`finally` block](exceptions.md#the-finally-block), so the code inside it runs when the coroutine is canceled.
Here, `CompletableDeferred` signals that the child coroutines are launched before they are canceled, but it doesn't guarantee that they start running. If they are canceled first, nothing is printed.

## Make coroutines react to cancellation {id="cancellation-is-cooperative"}

In Kotlin, coroutine cancellation is _cooperative_.
This means that coroutines only react to cancellation when they cooperate by [suspending](#suspension-points-and-cancellation) or [checking for cancellation explicitly](#check-for-cancellation-explicitly). We will also cover some typical usage patterns such as periodically calling the [`yield()`](#yield-often-in-non-suspending-code) suspending function in CPU-intensive code, and using [`runInterruptible()`](#interrupt-blocking-code-when-coroutines-are-canceled) to interrupt blocking code when coroutines are canceled.

Coroutines which react to cancellations are sometimes referred to as **cancelable coroutines**. In this section, you will learn how to create cancelable coroutines.

### Suspension points and cancellation

When a coroutine is canceled, it continues running until it reaches a point in the code where it may suspend, also known as a _suspension point_.
If the coroutine suspends there, the suspending function checks whether it has been canceled.
If it has, the coroutine stops and throws `CancellationException`.

A call to a `suspend` function is a suspension point, but it doesn't always suspend.
For example, when awaiting a `Deferred` result, the coroutine only suspends if that `Deferred` isn't completed yet.

Here's an example using common suspending functions that suspend, enabling the coroutine to check and stop when it's canceled:

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.sync.Mutex
import kotlinx.coroutines.channels.Channel
import kotlin.time.Duration.Companion.milliseconds
import kotlin.time.Duration

//sampleStart
suspend fun main() {
    withContext(Dispatchers.Default) {
        val childJobs = listOf(
            launch {
                // Suspends until canceled
                awaitCancellation()
            },
            launch {
                // Suspends until canceled
                delay(Duration.INFINITE)
            },
            launch {
                val channel = Channel<Int>()
                // Suspends while waiting for a value that is never sent
                channel.receive()
            },
            launch {
                val deferred = CompletableDeferred<Int>()
                // Suspends while waiting for a value that is never completed
                deferred.await()
            },
            launch {
                val mutex = Mutex(locked = true)
                // Suspends while waiting for a mutex that remains locked indefinitely
                mutex.lock()
            }
        )
        
        // Gives the child coroutines time to start and suspend
        delay(100.milliseconds)
        
        // Cancels all child coroutines
        childJobs.forEach { it.cancel() }
    }
    println("All child jobs completed!")
}
//sampleEnd
```
{kotlin-runnable="true" id="suspension-points-example"}

> All suspending functions in the `kotlinx.coroutines` library cooperate with cancellation because they use [`suspendCancellableCoroutine()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/suspend-cancellable-coroutine.html) internally, which checks for cancellation when the coroutine suspends.
> In contrast, custom suspending functions that use [`suspendCoroutine()`](https://kotlinlang.org/api/core/kotlin-stdlib/kotlin.coroutines/suspend-coroutine.html) don't react to cancellation.
>
{style="tip"}

### Check for cancellation explicitly

If a coroutine doesn't suspend for a long time, it doesn't stop when it's canceled.

In certain scenarios, you may use the [`isActive`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/is-active.html) property or the [`ensureActive()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/ensure-active.html) function to check if the coroutine was canceled. `isActive` is `false` when the coroutine is canceled and `ensureActive()` throws `CancellationException` if the coroutine is canceled.

However, you almost never need to check for cancellation explicitly. In most cases you can use `yield()`.

### `yield()` often in non-suspending code

In CPU-intensive computations and suspending code which is unlikely to suspend, call `yield()` periodically to let the current coroutine check for cancellation.

The [`yield()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/yield.html) function suspends the coroutine, releasing its current thread and giving other coroutines a chance to run on it. Suspending the coroutine lets it check for cancellation and throw `CancellationException` if it's canceled.

Thus `yield()` achieves two goals: lets other coroutines run, and allows checking for cancellations.

Use `yield` to allow other coroutines to run on the same thread or thread pool before one of them finishes:

```kotlin
import kotlinx.coroutines.*

//sampleStart
fun main() {
    // runBlocking uses the current thread for running all coroutines
    runBlocking {
        val coroutineCount = 5
        repeat(coroutineCount) { coroutineIndex ->
            launch {
                val id = coroutineIndex + 1
                repeat(5) { iterationIndex ->
                    val iteration = iterationIndex + 1
                    // Temporarily suspends to give other coroutines a chance to run
                    // Without this, the coroutines run sequentially
                    yield()
                    // Prints the coroutine index and iteration index
                    println("$id * $iteration = ${id * iteration}")
                }
            }
        }
    }
}
//sampleEnd
```
{kotlin-runnable="true" id="yield-example"}

In this example, each coroutine uses `yield()` to let other coroutines run between iterations.

### Interrupt blocking code when coroutines are canceled

On the JVM, some functions, such as `Thread.sleep()` or `BlockingQueue.take()`, can block the current thread.
These blocking functions can be interrupted, which stops them prematurely.
However, when you call them from a coroutine, cancellation doesn't interrupt the thread.

To interrupt the thread when canceling a coroutine, wrap the blocking code into the [`runInterruptible()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/run-interruptible.html) function:

```kotlin
import kotlinx.coroutines.*

//sampleStart
suspend fun main() {
    withContext(Dispatchers.Default) {
        val started = CompletableDeferred<Unit>()
        val job = launch {
            try {
                // Cancellation triggers a thread interruption
                runInterruptible {
                    started.complete(Unit)
                    try {
                        // Blocks the current thread for a very long time
                        Thread.sleep(Long.MAX_VALUE)
                    } catch (e: InterruptedException) {
                        println("Thread interrupted (Java): $e")
                        throw e
                    }
                }
            } catch (e: CancellationException) {
                println("Coroutine canceled (Kotlin): $e")
                throw e
            }
        }
        started.await()

        // Cancels the coroutine and interrupts the thread executing Thread.sleep()
        job.cancel()
    }
}
//sampleEnd
```
{kotlin-runnable="true" id="interrupt-cancellation-example"}

## Handle values safely when canceling coroutines

When a suspended coroutine is canceled, it resumes with a `CancellationException` instead of returning any values, even if those values are already available.
This behavior is called _prompt cancellation_.
It prevents your code from continuing in a canceled coroutine's scope, such as updating a screen that's already closed.

Here's an example:

```kotlin
// Defines a coroutine scope that uses the UI thread
class ScreenWithButtons(private val scope: CoroutineScope) {
    // Should only be called from the UI thread
    fun loadAndUpdateButtons(filename: String) {
        scope.launch {
            val buttonNames = withContext(Dispatchers.IO) {
                // Can be canceled here
                readLines(filename) // A blocking call, cannot be canceled here
                // Can be canceled here
            }
            // If withContext() returned a value, it wasn't canceled.
            // Now this coroutine runs on the UI thread again,
            // so no one can cancel this component's scope and dispose of buttons
            // until this coroutine suspends for the next time and releases the UI thread.
            // It's safe to call updateUi here, as buttons are guaranteed to exist.
            //
            // In other words, if the screen is canceled while withContext() is running,
            // the coroutine throws CancellationException instead of assigning a value
            // to buttonNames, so updateUi() is never called.
            updateUi(buttonNames)
        }
    }

    // Should only be called from the UI thread
    // Throws an exception if called after the user left the screen
    private fun updateUi(buttonNames: List<String>) {
        // Updates buttons with the specified names.

        // Throws if buttons no longer exist,
        // due to being disposed of
        // after the user left the screen.
    }

    // Should only be called from the UI thread
    fun leaveScreen() {
        // Cancels the scope when leaving the screen
        // You can no longer update the UI
        scope.cancel()
    }
}

// UI controller code
setHandler(Event.ScreenClosed) {
    // Always executes from the UI thread
    screenWithButtons.leaveScreen()
    buttons.dispose()
}
```

In this example, `withContext(Dispatchers.IO)` cooperates with cancellation and prevents `updateUi()` from running if the
`leaveScreen()` function cancels the coroutine before it returns the button names.

While prompt cancellation prevents using values after they are no longer valid, it can also stop your code while an important value is still in use, which might lead to losing that value.
This can happen when a coroutine receives a value, such as an `AutoCloseable` resource, but is canceled before it can reach the part of the code that closes it.
To prevent this, keep cleanup logic in a place that's guaranteed to run even when the coroutine receiving the value is canceled.

Here's an example:

```kotlin
import java.nio.file.*
import java.nio.charset.*
import kotlinx.coroutines.*
import java.io.*

// scope is a coroutine scope using the UI thread
class ScreenWithFileContents(private val scope: CoroutineScope) {
    fun displayFile(path: Path) {
        scope.launch {
            // Stores the reader in a variable, so the finally block can close it
            var reader: BufferedReader? = null
            
            try {
                withContext(Dispatchers.IO) {
                    reader = Files.newBufferedReader(
                        path, Charset.forName("US-ASCII")
                    )
                }
                // Uses the stored reader after withContext() completes
                updateUi(reader!!)
            } finally {
                // Ensures the reader is closed even when the coroutine is canceled
                reader?.close()
            }
        }
    }

    private suspend fun updateUi(reader: BufferedReader) {
        // Shows the file contents
        while (true) {
            val line = withContext(Dispatchers.IO) {
                reader.readLine()
            }
            if (line == null)
                break
            addOneLineToUi(line)
        }
    }

    private fun addOneLineToUi(line: String) {
        // Placeholder for code that adds one line to the UI
    }

    // Only callable from the UI thread
    fun leaveScreen() {
        // Cancels the scope when leaving the screen
        // You can no longer update the UI
        scope.cancel()
    }
}
```

In this example, storing the `BufferedReader` in a variable and closing it in the `finally` block ensures the resource is released even if the coroutine is canceled.

### Run non-cancelable blocks

You can prevent cancellation from affecting certain parts of a coroutine.
To do so, pass [`NonCancellable`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-non-cancellable/) as an argument to the `withContext()` coroutine builder function.

> Avoid using `NonCancellable` with other coroutine builders like `.launch()` or `.async()`. Doing so disrupts structured concurrency by breaking the parent-child relationship.
>
{style="warning"}

`NonCancellable` is useful when you need to ensure that certain operations, such as closing resources with a suspending `close()` function,
complete even if the coroutine is canceled before they finish.

Here's an example:

```kotlin
import kotlinx.coroutines.*
import kotlin.time.Duration.Companion.milliseconds

//sampleStart
val serviceStarted = CompletableDeferred<Unit>()

fun startService() {
    println("Starting the service...")
    serviceStarted.complete(Unit)
}

suspend fun shutdownServiceAndWait() {
    println("Shutting down...")
    delay(100.milliseconds)
    println("Successfully shut down!")
}

suspend fun main() {
    withContext(Dispatchers.Default) {
        val job = launch {
            startService()
            try {
                awaitCancellation()
            } finally {
                withContext(NonCancellable) {
                    // Without withContext(NonCancellable),
                    // this function doesn't complete because the coroutine is canceled
                    shutdownServiceAndWait()
                }
            }
        }
        serviceStarted.await()
        job.cancel()
    }
    println("Exiting the program")
}
//sampleEnd
```
{kotlin-runnable="true" id="noncancellable-blocks-example"}

## Timeout

A timeout allows you to automatically cancel a coroutine after a specified duration. It is useful for stopping operations that take too long. For example, if a request to download a picture from a server times-out, you can choose to retry, or fallback to the local cache.

To specify a timeout, use the [`withTimeoutOrNull()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/with-timeout-or-null.html) function with a `Duration`:

```kotlin
import kotlinx.coroutines.*
import kotlin.time.Duration.Companion.milliseconds

//sampleStart
suspend fun slowOperation(): String {
    try {
        delay(300.milliseconds)
        return "A"
    } catch (e: CancellationException) {
        println("The slow operation has been canceled: $e")
        throw e
    }
}

suspend fun fastOperation(): String {
    try {
        delay(15.milliseconds)
        return "B"
    } catch (e: CancellationException) {
        println("The fast operation has been canceled: $e")
        throw e
    }
}

suspend fun main() {
    withContext(Dispatchers.Default) {
        val slow = withTimeoutOrNull(100.milliseconds) {
            slowOperation()
        }
        println("The slow operation finished with $slow")
        val fast = withTimeoutOrNull(100.milliseconds) {
            fastOperation()
        }
        println("The fast operation finished with $fast")
    }
}
//sampleEnd
```
{kotlin-runnable="true" id="timeout-example"}

If the timeout exceeds the specified `Duration`, `withTimeoutOrNull()` returns `null`.
