<!--- INCLUDE .*/example-([a-z]+)-([0-9a-z]+)\.kt 
/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

// This file was automatically generated from coroutines-guide.md by Knit tool. Do not edit.
package kotlinx.coroutines.guide.$$1$$2
-->
<!--- KNIT     ../core/kotlinx-coroutines-core/test/guide/.*\.kt -->
<!--- TEST_OUT ../core/kotlinx-coroutines-core/test/guide/test/ExceptionsGuideTest.kt
// This file was automatically generated from coroutines-guide.md by Knit tool. Do not edit.
package kotlinx.coroutines.guide.test

import org.junit.Test

class ExceptionsGuideTest {
--> 
## Table of contents

<!--- TOC -->

* [Exception handling](#exception-handling)
  * [Exception propagation](#exception-propagation)
  * [CoroutineExceptionHandler](#coroutineexceptionhandler)
  * [Cancellation and exceptions](#cancellation-and-exceptions)
  * [Exceptions aggregation](#exceptions-aggregation)
* [Supervision](#supervision)
  * [Supervision job](#supervision-job)
  * [Supervision scope](#supervision-scope)
  * [Exceptions in supervised coroutines](#exceptions-in-supervised-coroutines)

<!--- END_TOC -->

## Exception handling


This section covers exception handling and cancellation on exceptions.
We already know that cancelled coroutine throws [CancellationException] in suspension points and that it 
is ignored by coroutines machinery. But what happens if an exception is thrown during cancellation or multiple children of the same 
coroutine throw an exception?

### Exception propagation

Coroutine builders come in two flavors: propagating exceptions automatically ([launch] and [actor]) or 
exposing them to users ([async] and [produce]).
The former treat exceptions as unhandled, similar to Java's `Thread.uncaughtExceptionHandler`, 
while the latter are relying on the user to consume the final 
exception, for example via [await][Deferred.await] or [receive][ReceiveChannel.receive] 
([produce] and [receive][ReceiveChannel.receive] are covered later in [Channels](https://github.com/Kotlin/kotlinx.coroutines/blob/master/docs/channels.md) section).

It can be demonstrated by a simple example that creates new coroutines in [GlobalScope]:

<div class="sample" markdown="1" theme="idea" data-highlight-only>

```kotlin
import kotlinx.coroutines.*

fun main() = runBlocking {
    val job = GlobalScope.launch {
        println("Throwing exception from launch")
        throw IndexOutOfBoundsException() // Will be printed to the console by Thread.defaultUncaughtExceptionHandler
    }
    job.join()
    println("Joined failed job")
    val deferred = GlobalScope.async {
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

</div>

> You can get full code [here](../core/kotlinx-coroutines-core/test/guide/example-exceptions-01.kt)

The output of this code is (with [debug](https://github.com/Kotlin/kotlinx.coroutines/blob/master/docs/coroutine-context-and-dispatchers.md#debugging-coroutines-and-threads)):

```text
Throwing exception from launch
Exception in thread "DefaultDispatcher-worker-2 @coroutine#2" java.lang.IndexOutOfBoundsException
Joined failed job
Throwing exception from async
Caught ArithmeticException
```

<!--- TEST EXCEPTION-->

### CoroutineExceptionHandler

But what if one does not want to print all exceptions to the console?
[CoroutineExceptionHandler] context element is used as generic `catch` block of coroutine where custom logging or exception handling may take place.
It is similar to using [`Thread.uncaughtExceptionHandler`](https://docs.oracle.com/javase/8/docs/api/java/lang/Thread.html#setUncaughtExceptionHandler(java.lang.Thread.UncaughtExceptionHandler)).

On JVM it is possible to redefine global exception handler for all coroutines by registering [CoroutineExceptionHandler] via
[`ServiceLoader`](https://docs.oracle.com/javase/8/docs/api/java/util/ServiceLoader.html).
Global exception handler is similar to 
[`Thread.defaultUncaughtExceptionHandler`](https://docs.oracle.com/javase/8/docs/api/java/lang/Thread.html#setDefaultUncaughtExceptionHandler(java.lang.Thread.UncaughtExceptionHandler)) 
which is used when no more specific handlers are registered.
On Android, `uncaughtExceptionPreHandler` is installed as a global coroutine exception handler.

[CoroutineExceptionHandler] is invoked only on exceptions which are not expected to be handled by the user, 
so registering it in [async] builder and the like of it has no effect.

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

```kotlin
import kotlinx.coroutines.*

fun main() = runBlocking {
//sampleStart
    val handler = CoroutineExceptionHandler { _, exception -> 
        println("Caught $exception") 
    }
    val job = GlobalScope.launch(handler) {
        throw AssertionError()
    }
    val deferred = GlobalScope.async(handler) {
        throw ArithmeticException() // Nothing will be printed, relying on user to call deferred.await()
    }
    joinAll(job, deferred)
//sampleEnd    
}
```

</div>

> You can get full code [here](../core/kotlinx-coroutines-core/test/guide/example-exceptions-02.kt)

The output of this code is:

```text
Caught java.lang.AssertionError
```

<!--- TEST-->

### Cancellation and exceptions

Cancellation is tightly bound with exceptions. Coroutines internally use `CancellationException` for cancellation, these
exceptions are ignored by all handlers, so they should be used only as the source of additional debug information, which can
be obtained by `catch` block.
When a coroutine is cancelled using [Job.cancel] without a cause, it terminates, but it does not cancel its parent.
Cancelling without cause is a mechanism for parent to cancel its children without cancelling itself. 

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

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

</div>

> You can get full code [here](../core/kotlinx-coroutines-core/test/guide/example-exceptions-03.kt)

The output of this code is:

```text
Cancelling child
Child is cancelled
Parent is not cancelled
```

<!--- TEST-->

If a coroutine encounters exception other than `CancellationException`, it cancels its parent with that exception. 
This behaviour cannot be overridden and is used to provide stable coroutines hierarchies for
[structured concurrency](https://github.com/Kotlin/kotlinx.coroutines/blob/master/docs/composing-suspending-functions.md#structured-concurrency-with-async) which do not depend on 
[CoroutineExceptionHandler] implementation.
The original exception is handled by the parent when all its children terminate.

> This also a reason why, in these examples, [CoroutineExceptionHandler] is always installed to a coroutine
that is created in [GlobalScope]. It does not make sense to install an exception handler to a coroutine that
is launched in the scope of the main [runBlocking], since the main coroutine is going to be always cancelled
when its child completes with exception despite the installed handler. 

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

```kotlin
import kotlinx.coroutines.*

fun main() = runBlocking {
//sampleStart
    val handler = CoroutineExceptionHandler { _, exception -> 
        println("Caught $exception") 
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

</div>

> You can get full code [here](../core/kotlinx-coroutines-core/test/guide/example-exceptions-04.kt)

The output of this code is:

```text
Second child throws an exception
Children are cancelled, but exception is not handled until all children terminate
The first child finished its non cancellable block
Caught java.lang.ArithmeticException
```
<!--- TEST-->

### Exceptions aggregation

What happens if multiple children of a coroutine throw an exception?
The general rule is "the first exception wins", so the first thrown exception is exposed to the handler.
But that may cause lost exceptions, for example if coroutine throws an exception in its `finally` block.
So, additional exceptions are suppressed. 

> One of the solutions would have been to report each exception separately, 
but then [Deferred.await] should have had the same mechanism to avoid behavioural inconsistency and this 
would cause implementation details of a coroutines (whether it had delegated parts of its work to its children or not)
to leak to its exception handler.


<!--- INCLUDE

import kotlinx.coroutines.exceptions.*
-->

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

```kotlin
import kotlinx.coroutines.*
import java.io.*

fun main() = runBlocking {
    val handler = CoroutineExceptionHandler { _, exception ->
        println("Caught $exception with suppressed ${exception.suppressed.contentToString()}")
    }
    val job = GlobalScope.launch(handler) {
        launch {
            try {
                delay(Long.MAX_VALUE)
            } finally {
                throw ArithmeticException()
            }
        }
        launch {
            delay(100)
            throw IOException()
        }
        delay(Long.MAX_VALUE)
    }
    job.join()  
}
```

</div>

> You can get full code [here](../core/kotlinx-coroutines-core/test/guide/example-exceptions-05.kt)

> Note: This above code will work properly only on JDK7+ that supports `suppressed` exceptions

The output of this code is:

```text
Caught java.io.IOException with suppressed [java.lang.ArithmeticException]
```

<!--- TEST-->

> Note, this mechanism currently works only on Java version 1.7+. 
Limitation on JS and Native is temporary and will be fixed in the future.

Cancellation exceptions are transparent and unwrapped by default:

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

```kotlin
import kotlinx.coroutines.*
import java.io.*

fun main() = runBlocking {
//sampleStart
    val handler = CoroutineExceptionHandler { _, exception ->
        println("Caught original $exception")
    }
    val job = GlobalScope.launch(handler) {
        val inner = launch {
            launch {
                launch {
                    throw IOException()
                }
            }
        }
        try {
            inner.join()
        } catch (e: CancellationException) {
            println("Rethrowing CancellationException with original cause")
            throw e
        }
    }
    job.join()
//sampleEnd    
}
```

</div>

> You can get full code [here](../core/kotlinx-coroutines-core/test/guide/example-exceptions-06.kt)

The output of this code is:

```text
Rethrowing CancellationException with original cause
Caught original java.io.IOException
```
<!--- TEST-->

## Supervision

As we have studied before, cancellation is a bidirectional relationship propagating through the whole
coroutines hierarchy. But what if unidirectional cancellation is required? 

Good example of such requirement can be a UI component with the job defined in its scope. If any of UI's child task
has failed, it is not always necessary to cancel (effectively kill) the whole UI component,
but if UI component is destroyed (and its job is cancelled), then it is necessary to fail all children jobs as their result is no longer required.

Another example is a server process that spawns several children jobs and needs to _supervise_
their execution, tracking their failures and restarting just those children jobs that had failed.

### Supervision job

For these purposes [SupervisorJob][SupervisorJob()] can be used. It is similar to a regular [Job][Job()] with the only exception that cancellation is propagated
only downwards. It is easy to demonstrate with an example:

<div class="sample" markdown="1" theme="idea" data-highlight-only>

```kotlin
import kotlinx.coroutines.*

fun main() = runBlocking {
    val supervisor = SupervisorJob()
    with(CoroutineScope(coroutineContext + supervisor)) {
        // launch the first child -- its exception is ignored for this example (don't do this in practice!)
        val firstChild = launch(CoroutineExceptionHandler { _, _ ->  }) {
            println("First child is failing")
            throw AssertionError("First child is cancelled")
        }
        // launch the second child
        val secondChild = launch {
            firstChild.join()
            // Cancellation of the first child is not propagated to the second child
            println("First child is cancelled: ${firstChild.isCancelled}, but second one is still active")
            try {
                delay(Long.MAX_VALUE)
            } finally {
                // But cancellation of the supervisor is propagated
                println("Second child is cancelled because supervisor is cancelled")
            }
        }
        // wait until the first child fails & completes
        firstChild.join()
        println("Cancelling supervisor")
        supervisor.cancel()
        secondChild.join()
    }
}
```

</div>

> You can get full code [here](../core/kotlinx-coroutines-core/test/guide/example-supervision-01.kt)

The output of this code is:

```text
First child is failing
First child is cancelled: true, but second one is still active
Cancelling supervisor
Second child is cancelled because supervisor is cancelled
```
<!--- TEST-->


### Supervision scope

For *scoped* concurrency [supervisorScope] can be used instead of [coroutineScope] for the same purpose. It propagates cancellation 
only in one direction and cancels all children only if it has failed itself. It also waits for all children before completion
just like [coroutineScope] does.

<div class="sample" markdown="1" theme="idea" data-highlight-only>

```kotlin
import kotlin.coroutines.*
import kotlinx.coroutines.*

fun main() = runBlocking {
    try {
        supervisorScope {
            val child = launch {
                try {
                    println("Child is sleeping")
                    delay(Long.MAX_VALUE)
                } finally {
                    println("Child is cancelled")
                }
            }
            // Give our child a chance to execute and print using yield 
            yield()
            println("Throwing exception from scope")
            throw AssertionError()
        }
    } catch(e: AssertionError) {
        println("Caught assertion error")
    }
}
```

</div>

> You can get full code [here](../core/kotlinx-coroutines-core/test/guide/example-supervision-02.kt)

The output of this code is:

```text
Child is sleeping
Throwing exception from scope
Child is cancelled
Caught assertion error
```
<!--- TEST-->

### Exceptions in supervised coroutines

Another crucial difference between regular and supervisor jobs is exception handling.
Every child should handle its exceptions by itself via exception handling mechanisms.
This difference comes from the fact that child's failure is not propagated to the parent.

<div class="sample" markdown="1" theme="idea" data-highlight-only>

```kotlin
import kotlin.coroutines.*
import kotlinx.coroutines.*

fun main() = runBlocking {
    val handler = CoroutineExceptionHandler { _, exception -> 
        println("Caught $exception") 
    }
    supervisorScope {
        val child = launch(handler) {
            println("Child throws an exception")
            throw AssertionError()
        }
        println("Scope is completing")
    }
    println("Scope is completed")
}
```

</div>

> You can get full code [here](../core/kotlinx-coroutines-core/test/guide/example-supervision-03.kt)

The output of this code is:

```text
Scope is completing
Child throws an exception
Caught java.lang.AssertionError
Scope is completed
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
[Job.cancel]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-job/cancel.html
[runBlocking]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/run-blocking.html
[SupervisorJob()]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-supervisor-job.html
[Job()]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-job.html
[supervisorScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/supervisor-scope.html
[coroutineScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/coroutine-scope.html
<!--- INDEX kotlinx.coroutines.channels -->
[actor]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/actor.html
[produce]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/produce.html
[ReceiveChannel.receive]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-receive-channel/receive.html
<!--- END -->
