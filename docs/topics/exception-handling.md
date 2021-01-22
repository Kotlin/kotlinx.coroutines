<!--- TEST_NAME ExceptionsGuideTest -->

[//]: # (title: Coroutine exceptions handling)

This section covers exception handling and cancellation on exceptions.
We already know that a cancelled coroutine throws [CancellationException] in suspension points and that it
is ignored by the coroutines' machinery. Here we look at what happens if an exception is thrown during cancellation or multiple children of the same
coroutine throw an exception.

## Exception propagation

Coroutine builders come in two flavors: propagating exceptions automatically ([launch] and [actor]) or
exposing them to users ([async] and [produce]).
When these builders are used to create a _root_ coroutine, that is not a _child_ of another coroutine,
the former builders treat exceptions as **uncaught** exceptions, similar to Java's `Thread.uncaughtExceptionHandler`,
while the latter are relying on the user to consume the final
exception, for example via [await][Deferred.await] or [receive][ReceiveChannel.receive] 
([produce] and [receive][ReceiveChannel.receive] are covered later in [Channels](https://github.com/Kotlin/kotlinx.coroutines/blob/master/docs/channels.md) section).

It can be demonstrated by a simple example that creates root coroutines using the [GlobalScope]:

```kotlin
import kotlinx.coroutines.*

fun main() = runBlocking {
    val job = GlobalScope.launch { // root coroutine with launch
        println("Throwing exception from launch")
        throw IndexOutOfBoundsException() // Will be printed to the console by Thread.defaultUncaughtExceptionHandler
    }
    job.join()
    println("Joined failed job")
    val deferred = GlobalScope.async { // root coroutine with async
        println("Throwing exception from async")
        throw ArithmeticException() // Nothing is printed, relying on user to call await
    }
    try {
        deferred.await()
        println("Unreached")
    } catch (e: ArithmeticException) {
        println("Caught ArithmeticException")
    }
}
```

> You can get the full code [here](../../kotlinx-coroutines-core/jvm/test/guide/example-exceptions-01.kt).
>
{type="note"}

The output of this code is (with [debug](https://github.com/Kotlin/kotlinx.coroutines/blob/master/docs/coroutine-context-and-dispatchers.md#debugging-coroutines-and-threads)):

```text
Throwing exception from launch
Exception in thread "DefaultDispatcher-worker-2 @coroutine#2" java.lang.IndexOutOfBoundsException
Joined failed job
Throwing exception from async
Caught ArithmeticException
```

<!--- TEST EXCEPTION-->

## CoroutineExceptionHandler

It is possible to customize the default behavior of printing **uncaught** exceptions to the console.
[CoroutineExceptionHandler] context element on a _root_ coroutine can be used as generic `catch` block for
this root coroutine and all its children where custom exception handling may take place.
It is similar to [`Thread.uncaughtExceptionHandler`](https://docs.oracle.com/javase/8/docs/api/java/lang/Thread.html#setUncaughtExceptionHandler(java.lang.Thread.UncaughtExceptionHandler)).
You cannot recover from the exception in the `CoroutineExceptionHandler`. The coroutine had already completed
with the corresponding exception when the handler is called. Normally, the handler is used to
log the exception, show some kind of error message, terminate, and/or restart the application.

On JVM it is possible to redefine global exception handler for all coroutines by registering [CoroutineExceptionHandler] via
[`ServiceLoader`](https://docs.oracle.com/javase/8/docs/api/java/util/ServiceLoader.html).
Global exception handler is similar to 
[`Thread.defaultUncaughtExceptionHandler`](https://docs.oracle.com/javase/8/docs/api/java/lang/Thread.html#setDefaultUncaughtExceptionHandler(java.lang.Thread.UncaughtExceptionHandler)) 
which is used when no more specific handlers are registered.
On Android, `uncaughtExceptionPreHandler` is installed as a global coroutine exception handler.

`CoroutineExceptionHandler` is invoked only on **uncaught** exceptions &mdash; exceptions that were not handled in any other way.
In particular, all _children_ coroutines (coroutines created in the context of another [Job]) delegate handling of
their exceptions to their parent coroutine, which also delegates to the parent, and so on until the root,
so the `CoroutineExceptionHandler` installed in their context is never used. 
In addition to that, [async] builder always catches all exceptions and represents them in the resulting [Deferred] object, 
so its `CoroutineExceptionHandler` has no effect either.

> Coroutines running in supervision scope do not propagate exceptions to their parent and are
> excluded from this rule. A further [Supervision](#supervision) section of this document gives more details.
>
{type="note"}  

```kotlin
import kotlinx.coroutines.*

fun main() = runBlocking {
//sampleStart
    val handler = CoroutineExceptionHandler { _, exception -> 
        println("CoroutineExceptionHandler got $exception") 
    }
    val job = GlobalScope.launch(handler) { // root coroutine, running in GlobalScope
        throw AssertionError()
    }
    val deferred = GlobalScope.async(handler) { // also root, but async instead of launch
        throw ArithmeticException() // Nothing will be printed, relying on user to call deferred.await()
    }
    joinAll(job, deferred)
//sampleEnd    
}
```
{kotlin-runnable="true" kotlin-min-compiler-version="1.3"}

> You can get the full code [here](../../kotlinx-coroutines-core/jvm/test/guide/example-exceptions-02.kt).
>
{type="note"}

The output of this code is:

```text
CoroutineExceptionHandler got java.lang.AssertionError
```

<!--- TEST-->

## Cancellation and exceptions

Cancellation is closely related to exceptions. Coroutines internally use `CancellationException` for cancellation, these
exceptions are ignored by all handlers, so they should be used only as the source of additional debug information, which can
be obtained by `catch` block.
When a coroutine is cancelled using [Job.cancel], it terminates, but it does not cancel its parent.

```kotlin
import kotlinx.coroutines.*

fun main() = runBlocking {
//sampleStart
    val job = launch {
        val child = launch {
            try {
                delay(Long.MAX_VALUE)
            } finally {
                println("Child is cancelled")
            }
        }
        yield()
        println("Cancelling child")
        child.cancel()
        child.join()
        yield()
        println("Parent is not cancelled")
    }
    job.join()
//sampleEnd    
}
```
{kotlin-runnable="true" kotlin-min-compiler-version="1.3"}

> You can get the full code [here](../../kotlinx-coroutines-core/jvm/test/guide/example-exceptions-03.kt).
>
{type="note"}

The output of this code is:

```text
Cancelling child
Child is cancelled
Parent is not cancelled
```

<!--- TEST-->

If a coroutine encounters an exception other than `CancellationException`, it cancels its parent with that exception. 
This behaviour cannot be overridden and is used to provide stable coroutines hierarchies for
[structured concurrency](https://github.com/Kotlin/kotlinx.coroutines/blob/master/docs/composing-suspending-functions.md#structured-concurrency-with-async).
[CoroutineExceptionHandler] implementation is not used for child coroutines.

> In these examples, [CoroutineExceptionHandler] is always installed to a coroutine
> that is created in [GlobalScope]. It does not make sense to install an exception handler to a coroutine that
> is launched in the scope of the main [runBlocking], since the main coroutine is going to be always cancelled
> when its child completes with exception despite the installed handler.
>
{type="note"}

The original exception is handled by the parent only when all its children terminate,
which is demonstrated by the following example.

```kotlin
import kotlinx.coroutines.*

fun main() = runBlocking {
//sampleStart
    val handler = CoroutineExceptionHandler { _, exception -> 
        println("CoroutineExceptionHandler got $exception") 
    }
    val job = GlobalScope.launch(handler) {
        launch { // the first child
            try {
                delay(Long.MAX_VALUE)
            } finally {
                withContext(NonCancellable) {
                    println("Children are cancelled, but exception is not handled until all children terminate")
                    delay(100)
                    println("The first child finished its non cancellable block")
                }
            }
        }
        launch { // the second child
            delay(10)
            println("Second child throws an exception")
            throw ArithmeticException()
        }
    }
    job.join()
//sampleEnd 
}
```
{kotlin-runnable="true" kotlin-min-compiler-version="1.3"}

> You can get the full code [here](../../kotlinx-coroutines-core/jvm/test/guide/example-exceptions-04.kt).
>
{type="note"}

The output of this code is:

```text
Second child throws an exception
Children are cancelled, but exception is not handled until all children terminate
The first child finished its non cancellable block
CoroutineExceptionHandler got java.lang.ArithmeticException
```

<!--- TEST-->

## Exceptions aggregation

When multiple children of a coroutine fail with an exception, the
general rule is "the first exception wins", so the first exception gets handled.
All additional exceptions that happen after the first one are attached to the first exception as suppressed ones. 

<!--- INCLUDE
import kotlinx.coroutines.exceptions.*
-->

```kotlin
import kotlinx.coroutines.*
import java.io.*

fun main() = runBlocking {
    val handler = CoroutineExceptionHandler { _, exception ->
        println("CoroutineExceptionHandler got $exception with suppressed ${exception.suppressed.contentToString()}")
    }
    val job = GlobalScope.launch(handler) {
        launch {
            try {
                delay(Long.MAX_VALUE) // it gets cancelled when another sibling fails with IOException
            } finally {
                throw ArithmeticException() // the second exception
            }
        }
        launch {
            delay(100)
            throw IOException() // the first exception
        }
        delay(Long.MAX_VALUE)
    }
    job.join()  
}
```
{kotlin-runnable="true" kotlin-min-compiler-version="1.3"}

> You can get the full code [here](../../kotlinx-coroutines-core/jvm/test/guide/example-exceptions-05.kt).
>
{type="note"}

> Note: This above code will work properly only on JDK7+ that supports `suppressed` exceptions
>
{type="note"}

The output of this code is:

```text
CoroutineExceptionHandler got java.io.IOException with suppressed [java.lang.ArithmeticException]
```

<!--- TEST-->

> Note that this mechanism currently only works on Java version 1.7+. 
> The JS and Native restrictions are temporary and will be lifted in the future.
>
{type="note"}

Cancellation exceptions are transparent and are unwrapped by default:

```kotlin
import kotlinx.coroutines.*
import java.io.*

fun main() = runBlocking {
//sampleStart
    val handler = CoroutineExceptionHandler { _, exception ->
        println("CoroutineExceptionHandler got $exception")
    }
    val job = GlobalScope.launch(handler) {
        val inner = launch { // all this stack of coroutines will get cancelled
            launch {
                launch {
                    throw IOException() // the original exception
                }
            }
        }
        try {
            inner.join()
        } catch (e: CancellationException) {
            println("Rethrowing CancellationException with original cause")
            throw e // cancellation exception is rethrown, yet the original IOException gets to the handler  
        }
    }
    job.join()
//sampleEnd    
}
```
{kotlin-runnable="true" kotlin-min-compiler-version="1.3"}

> You can get the full code [here](../../kotlinx-coroutines-core/jvm/test/guide/example-exceptions-06.kt).
>
{type="note"}

The output of this code is:

```text
Rethrowing CancellationException with original cause
CoroutineExceptionHandler got java.io.IOException
```

<!--- TEST-->

## Supervision

As we have studied before, cancellation is a bidirectional relationship propagating through the whole
hierarchy of coroutines. Let us take a look at the case when unidirectional cancellation is required. 

A good example of such a requirement is a UI component with the job defined in its scope. If any of the UI's child tasks
have failed, it is not always necessary to cancel (effectively kill) the whole UI component,
but if UI component is destroyed (and its job is cancelled), then it is necessary to fail all child jobs as their results are no longer needed.

Another example is a server process that spawns multiple child jobs and needs to _supervise_
their execution, tracking their failures and only restarting the failed ones.

### Supervision job

The [SupervisorJob][SupervisorJob()] can be used for these purposes. 
It is similar to a regular [Job][Job()] with the only exception that cancellation is propagated
only downwards. This can easily be demonstrated using the following example:

```kotlin
import kotlinx.coroutines.*

fun main() = runBlocking {
    val supervisor = SupervisorJob()
    with(CoroutineScope(coroutineContext + supervisor)) {
        // launch the first child -- its exception is ignored for this example (don't do this in practice!)
        val firstChild = launch(CoroutineExceptionHandler { _, _ ->  }) {
            println("The first child is failing")
            throw AssertionError("The first child is cancelled")
        }
        // launch the second child
        val secondChild = launch {
            firstChild.join()
            // Cancellation of the first child is not propagated to the second child
            println("The first child is cancelled: ${firstChild.isCancelled}, but the second one is still active")
            try {
                delay(Long.MAX_VALUE)
            } finally {
                // But cancellation of the supervisor is propagated
                println("The second child is cancelled because the supervisor was cancelled")
            }
        }
        // wait until the first child fails & completes
        firstChild.join()
        println("Cancelling the supervisor")
        supervisor.cancel()
        secondChild.join()
    }
}
```

> You can get the full code [here](../../kotlinx-coroutines-core/jvm/test/guide/example-supervision-01.kt).
>
{type="note"}

The output of this code is:

```text
The first child is failing
The first child is cancelled: true, but the second one is still active
Cancelling the supervisor
The second child is cancelled because the supervisor was cancelled
```

<!--- TEST-->

### Supervision scope

Instead of [coroutineScope][_coroutineScope], we can use [supervisorScope][_supervisorScope] for _scoped_ concurrency. It propagates the cancellation
in one direction only and cancels all its children only if it failed itself. It also waits for all children before completion
just like [coroutineScope][_coroutineScope] does.

```kotlin
import kotlin.coroutines.*
import kotlinx.coroutines.*

fun main() = runBlocking {
    try {
        supervisorScope {
            val child = launch {
                try {
                    println("The child is sleeping")
                    delay(Long.MAX_VALUE)
                } finally {
                    println("The child is cancelled")
                }
            }
            // Give our child a chance to execute and print using yield 
            yield()
            println("Throwing an exception from the scope")
            throw AssertionError()
        }
    } catch(e: AssertionError) {
        println("Caught an assertion error")
    }
}
```

> You can get the full code [here](../../kotlinx-coroutines-core/jvm/test/guide/example-supervision-02.kt).
>
{type="note"}

The output of this code is:

```text
The child is sleeping
Throwing an exception from the scope
The child is cancelled
Caught an assertion error
```

<!--- TEST-->

#### Exceptions in supervised coroutines

Another crucial difference between regular and supervisor jobs is exception handling.
Every child should handle its exceptions by itself via the exception handling mechanism.
This difference comes from the fact that child's failure does not propagate to the parent.
It means that coroutines launched directly inside the [supervisorScope][_supervisorScope] _do_ use the [CoroutineExceptionHandler]
that is installed in their scope in the same way as root coroutines do
(see the [CoroutineExceptionHandler](#coroutineexceptionhandler) section for details). 

```kotlin
import kotlin.coroutines.*
import kotlinx.coroutines.*

fun main() = runBlocking {
    val handler = CoroutineExceptionHandler { _, exception -> 
        println("CoroutineExceptionHandler got $exception") 
    }
    supervisorScope {
        val child = launch(handler) {
            println("The child throws an exception")
            throw AssertionError()
        }
        println("The scope is completing")
    }
    println("The scope is completed")
}
```

> You can get the full code [here](../../kotlinx-coroutines-core/jvm/test/guide/example-supervision-03.kt).
>
{type="note"}

The output of this code is:

```text
The scope is completing
The child throws an exception
CoroutineExceptionHandler got java.lang.AssertionError
The scope is completed
```

<!--- TEST-->

<!--- MODULE kotlinx-coroutines-core -->
<!--- INDEX kotlinx.coroutines -->

[CancellationException]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-cancellation-exception/index.html
[launch]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/launch.html
[async]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/async.html
[Deferred.await]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-deferred/await.html
[GlobalScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-global-scope/index.html
[CoroutineExceptionHandler]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-coroutine-exception-handler/index.html
[Job]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-job/index.html
[Deferred]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-deferred/index.html
[Job.cancel]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-job/cancel.html
[runBlocking]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/run-blocking.html
[SupervisorJob()]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-supervisor-job.html
[Job()]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-job.html
[_coroutineScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/coroutine-scope.html
[_supervisorScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/supervisor-scope.html

<!--- INDEX kotlinx.coroutines.channels -->

[actor]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/actor.html
[produce]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/produce.html
[ReceiveChannel.receive]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-receive-channel/receive.html

<!--- END -->