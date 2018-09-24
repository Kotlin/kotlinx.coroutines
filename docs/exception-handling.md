<!--- INCLUDE .*/example-([a-z]+)-([0-9a-z]+)\.kt 
/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

// This file was automatically generated from coroutines-guide.md by Knit tool. Do not edit.
package kotlinx.coroutines.experimental.guide.$$1$$2

import kotlinx.coroutines.experimental.*
-->
<!--- KNIT     ../core/kotlinx-coroutines-core/test/guide/.*\.kt -->
<!--- TEST_OUT ../core/kotlinx-coroutines-core/test/guide/test/ExceptionsGuideTest.kt
// This file was automatically generated from coroutines-guide.md by Knit tool. Do not edit.
package kotlinx.coroutines.experimental.guide.test

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

<!--- END_TOC -->

## Exception handling

<!--- INCLUDE .*/example-exceptions-([0-9]+).kt
-->

This section covers exception handling and cancellation on exceptions.
We already know that cancelled coroutine throws [CancellationException] in suspension points and that it 
is ignored by coroutines machinery. But what happens if an exception is thrown during cancellation or multiple children of the same 
coroutine throw an exception?

### Exception propagation

Coroutine builders come in two flavors: propagating exceptions automatically ([launch] and [actor]) or 
exposing them to users ([async] and [produce]).
The former treat exceptions as unhandled, similar to Java's `Thread.uncaughExceptionHandler`, 
while the latter are relying on the user to consume the final 
exception, for example via [await][Deferred.await] or [receive][ReceiveChannel.receive] 
([produce] and [receive][ReceiveChannel.receive] are covered later in [Channels](#channels) section).

It can be demonstrated by a simple example that creates new coroutines in [GlobalScope]:

```kotlin
fun main(args: Array<String>) = runBlocking {
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

> You can get full code [here](../core/kotlinx-coroutines-core/test/guide/example-exceptions-01.kt)

The output of this code is (with [debug](#debugging-coroutines-and-threads)):

```text
Throwing exception from launch
Exception in thread "ForkJoinPool.commonPool-worker-2 @coroutine#2" java.lang.IndexOutOfBoundsException
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

```kotlin
fun main(args: Array<String>) = runBlocking {
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
}
```

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

<!--- INCLUDE
import kotlin.coroutines.experimental.*
-->

```kotlin
fun main(args: Array<String>) = runBlocking {
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
}
```

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
[structured concurrency](#structured-concurrency) which do not depend on 
[CoroutineExceptionHandler] implementation.
The original exception is handled by the parent when all its children terminate.

> This also a reason why, in these examples, [CoroutineExceptionHandler] is always installed to a coroutine
that is created in [GlobalScope]. It does not make sense to install an exception handler to a coroutine that
is launched in the scope of the main [runBlocking], since the main coroutine is going to be always cancelled
when its child completes with exception despite the installed handler. 

<!--- INCLUDE
import kotlin.coroutines.experimental.*
-->

```kotlin
fun main(args: Array<String>) = runBlocking {
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
}
```

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
would cause implementation details of a coroutines (whether it had delegate parts of its work to its children or not)
to leak to its exception handler.

<!--- INCLUDE
import kotlinx.coroutines.experimental.exceptions.*
import kotlin.coroutines.experimental.*
import java.io.*
-->

```kotlin
fun main(args: Array<String>) = runBlocking {
    val handler = CoroutineExceptionHandler { _, exception ->
        println("Caught $exception with suppressed ${exception.suppressed().contentToString()}")
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
            throw IOException()
        }
        delay(Long.MAX_VALUE)
    }
    job.join()
}
```

> You can get full code [here](../core/kotlinx-coroutines-core/test/guide/example-exceptions-05.kt)

The output of this code is:

```text
Caught java.io.IOException with suppressed [java.lang.ArithmeticException]
```

<!--- TEST-->

> Note, this mechanism currently works only on Java version 1.7+. 
Limitation on JS and Native is temporary and will be fixed in the future.

Cancellation exceptions are transparent and unwrapped by default:

<!--- INCLUDE
import kotlin.coroutines.experimental.*
import java.io.*
-->

```kotlin
fun main(args: Array<String>) = runBlocking {
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
}
```

> You can get full code [here](../core/kotlinx-coroutines-core/test/guide/example-exceptions-06.kt)

The output of this code is:

```text
Rethrowing CancellationException with original cause
Caught original java.io.IOException
```
<!--- TEST-->

<!--- MODULE kotlinx-coroutines-core -->
<!--- INDEX kotlinx.coroutines.experimental -->
[CancellationException]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-cancellation-exception/index.html
[Deferred.await]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-deferred/await.html
[GlobalScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-global-scope/index.html
[CoroutineExceptionHandler]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-coroutine-exception-handler/index.html
[async]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/async.html
[Job.cancel]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-job/cancel.html
[runBlocking]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/run-blocking.html
<!--- INDEX kotlinx.coroutines.experimental.channels -->
[actor]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.channels/actor.html
[produce]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.channels/produce.html
[ReceiveChannel.receive]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.channels/-receive-channel/receive.html
<!--- END -->
