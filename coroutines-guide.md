<!--- INCLUDE .*/example-([a-z]+)-([0-9a-z]+)\.kt 
/*
 * Copyright 2016-2017 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// This file was automatically generated from coroutines-guide.md by Knit tool. Do not edit.
package guide.$$1.example$$2

import kotlinx.coroutines.experimental.*
-->
<!--- KNIT     core/kotlinx-coroutines-core/src/test/kotlin/guide/.*\.kt -->
<!--- TEST_OUT core/kotlinx-coroutines-core/src/test/kotlin/guide/test/GuideTest.kt
// This file was automatically generated from coroutines-guide.md by Knit tool. Do not edit.
package guide.test

import org.junit.Test

class GuideTest {
--> 

# Guide to kotlinx.coroutines by example

This is a guide on core features of `kotlinx.coroutines` with a series of examples.

## Introduction and setup

Kotlin, as a language, provides only minimal low-level APIs in its standard library to enable various other 
libraries to utilize coroutines. Unlike many other languages with similar capabilities, `async` and `await`
are not keywords in Kotlin and are not even part of its standard library.

`kotlinx.coroutines` is one such rich library. It contains a number of high-level 
coroutine-enabled primitives that this guide covers, including `launch`, `async` and others. 
You need to add a dependency on `kotlinx-coroutines-core` module as explained 
[here](README.md#using-in-your-projects) to use primitives from this guide in your projects.

## Table of contents

<!--- TOC -->

* [Coroutine basics](#coroutine-basics)
  * [Your first coroutine](#your-first-coroutine)
  * [Bridging blocking and non-blocking worlds](#bridging-blocking-and-non-blocking-worlds)
  * [Waiting for a job](#waiting-for-a-job)
  * [Extract function refactoring](#extract-function-refactoring)
  * [Coroutines ARE light-weight](#coroutines-are-light-weight)
  * [Coroutines are like daemon threads](#coroutines-are-like-daemon-threads)
* [Cancellation and timeouts](#cancellation-and-timeouts)
  * [Cancelling coroutine execution](#cancelling-coroutine-execution)
  * [Cancellation is cooperative](#cancellation-is-cooperative)
  * [Making computation code cancellable](#making-computation-code-cancellable)
  * [Closing resources with finally](#closing-resources-with-finally)
  * [Run non-cancellable block](#run-non-cancellable-block)
  * [Timeout](#timeout)
* [Composing suspending functions](#composing-suspending-functions)
  * [Sequential by default](#sequential-by-default)
  * [Concurrent using async](#concurrent-using-async)
  * [Lazily started async](#lazily-started-async)
  * [Async-style functions](#async-style-functions)
* [Coroutine context and dispatchers](#coroutine-context-and-dispatchers)
  * [Dispatchers and threads](#dispatchers-and-threads)
  * [Unconfined vs confined dispatcher](#unconfined-vs-confined-dispatcher)
  * [Debugging coroutines and threads](#debugging-coroutines-and-threads)
  * [Jumping between threads](#jumping-between-threads)
  * [Job in the context](#job-in-the-context)
  * [Children of a coroutine](#children-of-a-coroutine)
  * [Combining contexts](#combining-contexts)
  * [Parental responsibilities](#parental-responsibilities)
  * [Naming coroutines for debugging](#naming-coroutines-for-debugging)
  * [Cancellation via explicit job](#cancellation-via-explicit-job)
* [Channels](#channels)
  * [Channel basics](#channel-basics)
  * [Closing and iteration over channels](#closing-and-iteration-over-channels)
  * [Building channel producers](#building-channel-producers)
  * [Pipelines](#pipelines)
  * [Prime numbers with pipeline](#prime-numbers-with-pipeline)
  * [Fan-out](#fan-out)
  * [Fan-in](#fan-in)
  * [Buffered channels](#buffered-channels)
  * [Channels are fair](#channels-are-fair)
* [Shared mutable state and concurrency](#shared-mutable-state-and-concurrency)
  * [The problem](#the-problem)
  * [Volatiles are of no help](#volatiles-are-of-no-help)
  * [Thread-safe data structures](#thread-safe-data-structures)
  * [Thread confinement fine-grained](#thread-confinement-fine-grained)
  * [Thread confinement coarse-grained](#thread-confinement-coarse-grained)
  * [Mutual exclusion](#mutual-exclusion)
  * [Actors](#actors)
* [Select expression](#select-expression)
  * [Selecting from channels](#selecting-from-channels)
  * [Selecting on close](#selecting-on-close)
  * [Selecting to send](#selecting-to-send)
  * [Selecting deferred values](#selecting-deferred-values)
  * [Switch over a channel of deferred values](#switch-over-a-channel-of-deferred-values)
* [Further reading](#further-reading)

<!--- END_TOC -->

## Coroutine basics

This section covers basic coroutine concepts.

### Your first coroutine

Run the following code:

```kotlin
fun main(args: Array<String>) {
    launch { // launch new coroutine in background and continue
        delay(1000L) // non-blocking delay for 1 second (default time unit is ms)
        println("World!") // print after delay
    }
    println("Hello,") // main thread continues while coroutine is delayed
    Thread.sleep(2000L) // block main thread for 2 seconds to keep JVM alive
}
```

> You can get full code [here](core/kotlinx-coroutines-core/src/test/kotlin/guide/example-basic-01.kt)

Run this code:

```text
Hello,
World!
```

<!--- TEST -->

Essentially, coroutines are light-weight threads.
They are launched with [launch] _coroutine builder_.
You can achieve the same result replacing
`launch { ... }` with `thread { ... }` and `delay(...)` with `Thread.sleep(...)`. Try it.

If you start by replacing `launch` by `thread`, the compiler produces the following error:

```
Error: Kotlin: Suspend functions are only allowed to be called from a coroutine or another suspend function
```

That is because [delay] is a special _suspending function_ that does not block a thread, but _suspends_
coroutine and it can be only used from a coroutine.

### Bridging blocking and non-blocking worlds

The first example mixes _non-blocking_ `delay(...)` and _blocking_ `Thread.sleep(...)` in the same code. 
It is easy to get lost which one is blocking and which one is not. 
Let's be explicit about blocking using [runBlocking] coroutine builder:

```kotlin
fun main(args: Array<String>) { 
    launch { // launch new coroutine in background and continue
        delay(1000L)
        println("World!")
    }
    println("Hello,") // main thread continues here immediately
    runBlocking {     // but this expression blocks the main thread
        delay(2000L)  // ... while we delay for 2 seconds to keep JVM alive
    } 
}
```

> You can get full code [here](core/kotlinx-coroutines-core/src/test/kotlin/guide/example-basic-02.kt)

<!--- TEST
Hello,
World!
-->

The result is the same, but this code uses only non-blocking [delay]. 
The main thread, that invokes `runBlocking`, _blocks_ until the coroutine inside `runBlocking` completes. 

This example can be also rewritten in a more idiomatic way, using `runBlocking` to wrap 
the execution of the main function:

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> { // start main coroutine
    launch { // launch new coroutine in background and continue
        delay(1000L)
        println("World!")
    }
    println("Hello,") // main coroutine continues here immediately
    delay(2000L)      // delaying for 2 seconds to keep JVM alive
}
```

> You can get full code [here](core/kotlinx-coroutines-core/src/test/kotlin/guide/example-basic-02b.kt)

<!--- TEST
Hello,
World!
-->

Here `runBlocking<Unit> { ... }` works as an adaptor that is used to start the top-level main coroutine. 
We explicitly specify its `Unit` return type, because a well-formed `main` function in Kotlin has to return `Unit`.

This is also a way to write unit-tests for suspending functions:
 
```kotlin
class MyTest {
    @Test
    fun testMySuspendingFunction() = runBlocking<Unit> {
        // here we can use suspending functions using any assertion style that we like
    }
}
```

<!--- CLEAR -->
 
### Waiting for a job

Delaying for a time while another coroutine is working is not a good approach. Let's explicitly 
wait (in a non-blocking way) until the background [Job] that we have launched is complete:

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    val job = launch { // launch new coroutine and keep a reference to its Job
        delay(1000L)
        println("World!")
    }
    println("Hello,")
    job.join() // wait until child coroutine completes
}
```

> You can get full code [here](core/kotlinx-coroutines-core/src/test/kotlin/guide/example-basic-03.kt)

<!--- TEST
Hello,
World!
-->

Now the result is still the same, but the code of the main coroutine is not tied to the duration of
the background job in any way. Much better.

### Extract function refactoring

Let's extract the block of code inside `launch { ... }` into a separate function. When you 
perform "Extract function" refactoring on this code you get a new function with `suspend` modifier.
That is your first _suspending function_. Suspending functions can be used inside coroutines
just like regular functions, but their additional feature is that they can, in turn, 
use other suspending functions, like `delay` in this example, to _suspend_ execution of a coroutine.

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    val job = launch { doWorld() }
    println("Hello,")
    job.join()
}

// this is your first suspending function
suspend fun doWorld() {
    delay(1000L)
    println("World!")
}
```

> You can get full code [here](core/kotlinx-coroutines-core/src/test/kotlin/guide/example-basic-04.kt)

<!--- TEST
Hello,
World!
-->

### Coroutines ARE light-weight

Run the following code:

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    val jobs = List(100_000) { // launch a lot of coroutines and list their jobs
        launch {
            delay(1000L)
            print(".")
        }
    }
    jobs.forEach { it.join() } // wait for all jobs to complete
}
```

> You can get full code [here](core/kotlinx-coroutines-core/src/test/kotlin/guide/example-basic-05.kt)

<!--- TEST lines.size == 1 && lines[0] == ".".repeat(100_000) -->

It launches 100K coroutines and, after a second, each coroutine prints a dot. 
Now, try that with threads. What would happen? (Most likely your code will produce some sort of out-of-memory error)

### Coroutines are like daemon threads

The following code launches a long-running coroutine that prints "I'm sleeping" twice a second and then 
returns from the main function after some delay:

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    launch {
        repeat(1000) { i ->
            println("I'm sleeping $i ...")
            delay(500L)
        }
    }
    delay(1300L) // just quit after delay
}
```

> You can get full code [here](core/kotlinx-coroutines-core/src/test/kotlin/guide/example-basic-06.kt)

You can run and see that it prints three lines and terminates:

```text
I'm sleeping 0 ...
I'm sleeping 1 ...
I'm sleeping 2 ...
```

<!--- TEST -->

Active coroutines do not keep the process alive. They are like daemon threads.

## Cancellation and timeouts

This section covers coroutine cancellation and timeouts.

### Cancelling coroutine execution

In small application the return from "main" method might sound like a good idea to get all coroutines 
implicitly terminated. In a larger, long-running application, you need finer-grained control.
The [launch] function returns a [Job] that can be used to cancel running coroutine:
 
```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    val job = launch {
        repeat(1000) { i ->
            println("I'm sleeping $i ...")
            delay(500L)
        }
    }
    delay(1300L) // delay a bit
    println("main: I'm tired of waiting!")
    job.cancel() // cancels the job
    job.join() // waits for job's completion 
    println("main: Now I can quit.")
}
``` 

> You can get full code [here](core/kotlinx-coroutines-core/src/test/kotlin/guide/example-cancel-01.kt)

It produces the following output:

```text
I'm sleeping 0 ...
I'm sleeping 1 ...
I'm sleeping 2 ...
main: I'm tired of waiting!
main: Now I can quit.
```

<!--- TEST -->

As soon as main invokes `job.cancel`, we don't see any output from the other coroutine because it was cancelled. 
There is also a [Job] extension function [cancelAndJoin] 
that combines [cancel][Job.cancel] and [join][Job.join] invocations.

### Cancellation is cooperative

Coroutine cancellation is _cooperative_. A coroutine code has to cooperate to be cancellable.
All the suspending functions in `kotlinx.coroutines` are _cancellable_. They check for cancellation of 
coroutine and throw [CancellationException] when cancelled. However, if a coroutine is working in 
a computation and does not check for cancellation, then it cannot be cancelled, like the following 
example shows:

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    val startTime = System.currentTimeMillis()
    val job = launch {
        var nextPrintTime = startTime
        var i = 0
        while (i < 5) { // computation loop, just wastes CPU
            // print a message twice a second
            if (System.currentTimeMillis() >= nextPrintTime) {
                println("I'm sleeping ${i++} ...")
                nextPrintTime += 500L
            }
        }
    }
    delay(1300L) // delay a bit
    println("main: I'm tired of waiting!")
    job.cancelAndJoin() // cancels the job and waits for its completion
    println("main: Now I can quit.")
}
```

> You can get full code [here](core/kotlinx-coroutines-core/src/test/kotlin/guide/example-cancel-02.kt)

Run it to see that it continues to print "I'm sleeping" even after cancellation
until the job completes by itself after five iterations.

<!--- TEST 
I'm sleeping 0 ...
I'm sleeping 1 ...
I'm sleeping 2 ...
main: I'm tired of waiting!
I'm sleeping 3 ...
I'm sleeping 4 ...
main: Now I can quit.
-->

### Making computation code cancellable

There are two approaches to making computation code cancellable. The first one is to periodically 
invoke a suspending function that checks for cancellation. There is a [yield] function that is a good choice for that purpose.
The other one is to explicitly check the cancellation status. Let us try the later approach. 

Replace `while (i < 5)` in the previous example with `while (isActive)` and rerun it. 

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    val startTime = System.currentTimeMillis()
    val job = launch {
        var nextPrintTime = startTime
        var i = 0
        while (isActive) { // cancellable computation loop
            // print a message twice a second
            if (System.currentTimeMillis() >= nextPrintTime) {
                println("I'm sleeping ${i++} ...")
                nextPrintTime += 500L
            }
        }
    }
    delay(1300L) // delay a bit
    println("main: I'm tired of waiting!")
    job.cancelAndJoin() // cancels the job and waits for its completion
    println("main: Now I can quit.")
}
```

> You can get full code [here](core/kotlinx-coroutines-core/src/test/kotlin/guide/example-cancel-03.kt)

As you can see, now this loop is cancelled. [isActive][CoroutineScope.isActive] is a property that is available inside
the code of coroutines via [CoroutineScope] object.

<!--- TEST
I'm sleeping 0 ...
I'm sleeping 1 ...
I'm sleeping 2 ...
main: I'm tired of waiting!
main: Now I can quit.
-->

### Closing resources with finally

Cancellable suspending functions throw [CancellationException] on cancellation which can be handled in 
all the usual way. For example, `try {...} finally {...}` expression and Kotlin `use` function execute their
finalization actions normally when coroutine is cancelled:
 
```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    val job = launch {
        try {
            repeat(1000) { i ->
                println("I'm sleeping $i ...")
                delay(500L)
            }
        } finally {
            println("I'm running finally")
        }
    }
    delay(1300L) // delay a bit
    println("main: I'm tired of waiting!")
    job.cancelAndJoin() // cancels the job and waits for its completion
    println("main: Now I can quit.")
}
``` 

> You can get full code [here](core/kotlinx-coroutines-core/src/test/kotlin/guide/example-cancel-04.kt)

Both [join][Job.join] and [cancelAndJoin] wait for all the finalization actions to complete, 
so the example above produces the following output:

```text
I'm sleeping 0 ...
I'm sleeping 1 ...
I'm sleeping 2 ...
main: I'm tired of waiting!
I'm running finally
main: Now I can quit.
```

<!--- TEST -->

### Run non-cancellable block

Any attempt to use a suspending function in the `finally` block of the previous example will cause
[CancellationException], because the coroutine running this code is cancelled. Usually, this is not a 
problem, since all well-behaving closing operations (closing a file, cancelling a job, or closing any kind of a 
communication channel) are usually non-blocking and do not involve any suspending functions. However, in the 
rare case when you need to suspend in the cancelled coroutine you can wrap the corresponding code in
`withContext(NonCancellable) {...}` using [withContext] function and [NonCancellable] context as the following example shows:
 
```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    val job = launch {
        try {
            repeat(1000) { i ->
                println("I'm sleeping $i ...")
                delay(500L)
            }
        } finally {
            withContext(NonCancellable) {
                println("I'm running finally")
                delay(1000L)
                println("And I've just delayed for 1 sec because I'm non-cancellable")
            }
        }
    }
    delay(1300L) // delay a bit
    println("main: I'm tired of waiting!")
    job.cancelAndJoin() // cancels the job and waits for its completion
    println("main: Now I can quit.")
}
``` 

> You can get full code [here](core/kotlinx-coroutines-core/src/test/kotlin/guide/example-cancel-05.kt)

<!--- TEST
I'm sleeping 0 ...
I'm sleeping 1 ...
I'm sleeping 2 ...
main: I'm tired of waiting!
I'm running finally
And I've just delayed for 1 sec because I'm non-cancellable
main: Now I can quit.
-->

### Timeout

The most obvious reason to cancel coroutine execution in practice, 
is because its execution time has exceeded some timeout.
While you can manually track the reference to the corresponding [Job] and launch a separate coroutine to cancel 
the tracked one after delay, there is a ready to use [withTimeout] function that does it.
Look at the following example:

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    withTimeout(1300L) {
        repeat(1000) { i ->
            println("I'm sleeping $i ...")
            delay(500L)
        }
    }
}
```

> You can get full code [here](core/kotlinx-coroutines-core/src/test/kotlin/guide/example-cancel-06.kt)

It produces the following output:

```text
I'm sleeping 0 ...
I'm sleeping 1 ...
I'm sleeping 2 ...
Exception in thread "main" kotlinx.coroutines.experimental.TimeoutCancellationException: Timed out waiting for 1300 MILLISECONDS
```

<!--- TEST STARTS_WITH -->

The `TimeoutCancellationException` that is thrown by [withTimeout] is a subclass of [CancellationException].
We have not seen its stack trace printed on the console before. That is because
inside a cancelled coroutine `CancellationException` is considered to be a normal reason for coroutine completion. 
However, in this example we have used `withTimeout` right inside the `main` function. 

Because cancellation is just an exception, all the resources will be closed in a usual way. 
You can wrap the code with timeout in `try {...} catch (e: TimeoutCancellationException) {...}` block if 
you need to do some additional action specifically on any kind of timeout or use [withTimeoutOrNull] function
that is similar to [withTimeout], but returns `null` on timeout instead of throwing an exception:

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    val result = withTimeoutOrNull(1300L) {
        repeat(1000) { i ->
            println("I'm sleeping $i ...")
            delay(500L)
        }
        "Done" // will get cancelled before it produces this result
    }
    println("Result is $result")
}
```

> You can get full code [here](core/kotlinx-coroutines-core/src/test/kotlin/guide/example-cancel-07.kt)

There is no longer an exception when running this code:

```text
I'm sleeping 0 ...
I'm sleeping 1 ...
I'm sleeping 2 ...
Result is null
```

<!--- TEST -->

## Composing suspending functions

This section covers various approaches to composition of suspending functions.

### Sequential by default

Assume that we have two suspending functions defined elsewhere that do something useful like some kind of 
remote service call or computation. We just pretend they are useful, but actually each one just
delays for a second for the purpose of this example:

<!--- INCLUDE .*/example-compose-([0-9]+).kt
import kotlin.system.measureTimeMillis
-->

```kotlin
suspend fun doSomethingUsefulOne(): Int {
    delay(1000L) // pretend we are doing something useful here
    return 13
}

suspend fun doSomethingUsefulTwo(): Int {
    delay(1000L) // pretend we are doing something useful here, too
    return 29
}
```

<!--- INCLUDE .*/example-compose-([0-9]+).kt -->

What do we do if need to invoke them _sequentially_ -- first `doSomethingUsefulOne` _and then_ 
`doSomethingUsefulTwo` and compute the sum of their results? 
In practice we do this if we use the results of the first function to make a decision on whether we need 
to invoke the second one or to decide on how to invoke it.

We just use a normal sequential invocation, because the code in the coroutine, just like in the regular 
code, is _sequential_ by default. The following example demonstrates it by measuring the total 
time it takes to execute both suspending functions:

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    val time = measureTimeMillis {
        val one = doSomethingUsefulOne()
        val two = doSomethingUsefulTwo()
        println("The answer is ${one + two}")
    }
    println("Completed in $time ms")
}
```

> You can get full code [here](core/kotlinx-coroutines-core/src/test/kotlin/guide/example-compose-01.kt)

It produces something like this:

```text
The answer is 42
Completed in 2017 ms
```

<!--- TEST ARBITRARY_TIME -->

### Concurrent using async

What if there are no dependencies between invocation of `doSomethingUsefulOne` and `doSomethingUsefulTwo` and
we want to get the answer faster, by doing both _concurrently_? This is where [async] comes to help. 
 
Conceptually, [async] is just like [launch]. It starts a separate coroutine which is a light-weight thread 
that works concurrently with all the other coroutines. The difference is that `launch` returns a [Job] and 
does not carry any resulting value, while `async` returns a [Deferred] -- a light-weight non-blocking future
that represents a promise to provide a result later. You can use `.await()` on a deferred value to get its eventual result,
but `Deferred` is also a `Job`, so you can cancel it if needed.
 
```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    val time = measureTimeMillis {
        val one = async { doSomethingUsefulOne() }
        val two = async { doSomethingUsefulTwo() }
        println("The answer is ${one.await() + two.await()}")
    }
    println("Completed in $time ms")
}
```

> You can get full code [here](core/kotlinx-coroutines-core/src/test/kotlin/guide/example-compose-02.kt)

It produces something like this:

```text
The answer is 42
Completed in 1017 ms
```

<!--- TEST ARBITRARY_TIME -->

This is twice as fast, because we have concurrent execution of two coroutines. 
Note, that concurrency with coroutines is always explicit.

### Lazily started async

There is a laziness option to [async] using an optional `start` parameter with a value of [CoroutineStart.LAZY]. 
It starts coroutine only when its result is needed by some 
[await][Deferred.await] or if a [start][Job.start] function 
is invoked. Run the following example that differs from the previous one only by this option:

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    val time = measureTimeMillis {
        val one = async(start = CoroutineStart.LAZY) { doSomethingUsefulOne() }
        val two = async(start = CoroutineStart.LAZY) { doSomethingUsefulTwo() }
        println("The answer is ${one.await() + two.await()}")
    }
    println("Completed in $time ms")
}
```

> You can get full code [here](core/kotlinx-coroutines-core/src/test/kotlin/guide/example-compose-03.kt)

It produces something like this:

```text
The answer is 42
Completed in 2017 ms
```

<!--- TEST ARBITRARY_TIME -->

So, we are back to sequential execution, because we _first_ start and await for `one`, _and then_ start and await
for `two`. It is not the intended use-case for laziness. It is designed as a replacement for
the standard `lazy` function in cases when computation of the value involves suspending functions.

### Async-style functions

We can define async-style functions that invoke `doSomethingUsefulOne` and `doSomethingUsefulTwo`
_asynchronously_ using [async] coroutine builder. It is a good style to name such functions with 
"Async" suffix to highlight the fact that they only start asynchronous computation and one needs
to use the resulting deferred value to get the result.

```kotlin
// The result type of somethingUsefulOneAsync is Deferred<Int>
fun somethingUsefulOneAsync() = async {
    doSomethingUsefulOne()
}

// The result type of somethingUsefulTwoAsync is Deferred<Int>
fun somethingUsefulTwoAsync() = async {
    doSomethingUsefulTwo()
}
```

Note, that these `xxxAsync` functions are **not** _suspending_ functions. They can be used from anywhere.
However, their use always implies asynchronous (here meaning _concurrent_) execution of their action
with the invoking code.
 
The following example shows their use outside of coroutine:  
 
```kotlin
// note, that we don't have `runBlocking` to the right of `main` in this example
fun main(args: Array<String>) {
    val time = measureTimeMillis {
        // we can initiate async actions outside of a coroutine
        val one = somethingUsefulOneAsync()
        val two = somethingUsefulTwoAsync()
        // but waiting for a result must involve either suspending or blocking.
        // here we use `runBlocking { ... }` to block the main thread while waiting for the result
        runBlocking {
            println("The answer is ${one.await() + two.await()}")
        }
    }
    println("Completed in $time ms")
}
```

> You can get full code [here](core/kotlinx-coroutines-core/src/test/kotlin/guide/example-compose-04.kt)

<!--- TEST ARBITRARY_TIME
The answer is 42
Completed in 1085 ms
-->

## Coroutine context and dispatchers

Coroutines always execute in some context which is represented by the value of 
[CoroutineContext](https://kotlinlang.org/api/latest/jvm/stdlib/kotlin.coroutines.experimental/-coroutine-context/) 
type, defined in the Kotlin standard library.

The coroutine context is a set of various elements. The main elements are the [Job] of the coroutine, 
which we've seen before, and its dispatcher, which is covered in this section.

### Dispatchers and threads

Coroutine context includes a _coroutine dispatcher_ (see [CoroutineDispatcher]) that determines what thread or threads 
the corresponding coroutine uses for its execution. Coroutine dispatcher can confine coroutine execution 
to a specific thread, dispatch it to a thread pool, or let it run unconfined. 

All coroutines builders like [launch] and [async] accept an optional 
[CoroutineContext](https://kotlinlang.org/api/latest/jvm/stdlib/kotlin.coroutines.experimental/-coroutine-context/) 
parameter that can be used to explicitly specify the dispatcher for new coroutine and other context elements. 

Try the following example:

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    val jobs = arrayListOf<Job>()
    jobs += launch(Unconfined) { // not confined -- will work with main thread
        println("      'Unconfined': I'm working in thread ${Thread.currentThread().name}")
    }
    jobs += launch(coroutineContext) { // context of the parent, runBlocking coroutine
        println("'coroutineContext': I'm working in thread ${Thread.currentThread().name}")
    }
    jobs += launch(CommonPool) { // will get dispatched to ForkJoinPool.commonPool (or equivalent)
        println("      'CommonPool': I'm working in thread ${Thread.currentThread().name}")
    }
    jobs += launch(newSingleThreadContext("MyOwnThread")) { // will get its own new thread
        println("          'newSTC': I'm working in thread ${Thread.currentThread().name}")
    }
    jobs.forEach { it.join() }
}
```

> You can get full code [here](core/kotlinx-coroutines-core/src/test/kotlin/guide/example-context-01.kt)

It produces the following output (maybe in different order):

```text
      'Unconfined': I'm working in thread main
      'CommonPool': I'm working in thread ForkJoinPool.commonPool-worker-1
          'newSTC': I'm working in thread MyOwnThread
'coroutineContext': I'm working in thread main
```

<!--- TEST LINES_START_UNORDERED -->

The default dispatcher that we've used in previous sections is representend by [DefaultDispatcher], which 
is equal to [CommonPool] in the current implementation. So, `launch { ... }` is the same 
as `launch(DefaultDispatcher) { ... }`, which is the same as `launch(CommonPool) { ... }`. 

The difference between parent [coroutineContext][CoroutineScope.coroutineContext] and
[Unconfined] context will be shown later.

Note, that [newSingleThreadContext] creates a new thread, which is a very expensive resource. 
In a real application it must be either released, when no longer needed, using [close][ThreadPoolDispatcher.close] 
function, or stored in a top-level variable and reused throughout the application.  

### Unconfined vs confined dispatcher
 
The [Unconfined] coroutine dispatcher starts coroutine in the caller thread, but only until the
first suspension point. After suspension it resumes in the thread that is fully determined by the
suspending function that was invoked. Unconfined dispatcher is appropriate when coroutine does not
consume CPU time nor updates any shared data (like UI) that is confined to a specific thread. 

On the other side, [coroutineContext][CoroutineScope.coroutineContext] property that is available inside the block of any coroutine
via [CoroutineScope] interface, is a reference to a context of this particular coroutine. 
This way, a parent context can be inherited. The default dispatcher for [runBlocking] coroutine, in particular,
is confined to the invoker thread, so inheriting it has the effect of confining execution to
this thread with a predictable FIFO scheduling.

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    val jobs = arrayListOf<Job>()
    jobs += launch(Unconfined) { // not confined -- will work with main thread
        println("      'Unconfined': I'm working in thread ${Thread.currentThread().name}")
        delay(500)
        println("      'Unconfined': After delay in thread ${Thread.currentThread().name}")
    }
    jobs += launch(coroutineContext) { // context of the parent, runBlocking coroutine
        println("'coroutineContext': I'm working in thread ${Thread.currentThread().name}")
        delay(1000)
        println("'coroutineContext': After delay in thread ${Thread.currentThread().name}")
    }
    jobs.forEach { it.join() }
}
```

> You can get full code [here](core/kotlinx-coroutines-core/src/test/kotlin/guide/example-context-02.kt)

Produces the output: 
 
```text
      'Unconfined': I'm working in thread main
'coroutineContext': I'm working in thread main
      'Unconfined': After delay in thread kotlinx.coroutines.DefaultExecutor
'coroutineContext': After delay in thread main
```

<!--- TEST LINES_START -->
 
So, the coroutine that had inherited `coroutineContext` of `runBlocking {...}` continues to execute
in the `main` thread, while the unconfined one had resumed in the default executor thread that [delay]
function is using.

### Debugging coroutines and threads

Coroutines can suspend on one thread and resume on another thread with [Unconfined] dispatcher or 
with a default multi-threaded dispatcher. Even with a single-threaded dispatcher it might be hard to
figure out what coroutine was doing what, where, and when. The common approach to debugging applications with 
threads is to print the thread name in the log file on each log statement. This feature is universally supported
by logging frameworks. When using coroutines, the thread name alone does not give much of a context, so 
`kotlinx.coroutines` includes debugging facilities to make it easier. 

Run the following code with `-Dkotlinx.coroutines.debug` JVM option:

```kotlin
fun log(msg: String) = println("[${Thread.currentThread().name}] $msg")

fun main(args: Array<String>) = runBlocking<Unit> {
    val a = async(coroutineContext) {
        log("I'm computing a piece of the answer")
        6
    }
    val b = async(coroutineContext) {
        log("I'm computing another piece of the answer")
        7
    }
    log("The answer is ${a.await() * b.await()}")
}
```

> You can get full code [here](core/kotlinx-coroutines-core/src/test/kotlin/guide/example-context-03.kt)

There are three coroutines. The main coroutine (#1) -- `runBlocking` one, 
and two coroutines computing deferred values `a` (#2) and `b` (#3).
They are all executing in the context of `runBlocking` and are confined to the main thread.
The output of this code is:

```text
[main @coroutine#2] I'm computing a piece of the answer
[main @coroutine#3] I'm computing another piece of the answer
[main @coroutine#1] The answer is 42
```

<!--- TEST FLEXIBLE_THREAD -->

The `log` function prints the name of the thread in square brackets and you can see, that it is the `main`
thread, but the identifier of the currently executing coroutine is appended to it. This identifier 
is consecutively assigned to all created coroutines when debugging mode is turned on.

You can read more about debugging facilities in the documentation for [newCoroutineContext] function.

### Jumping between threads

Run the following code with `-Dkotlinx.coroutines.debug` JVM option:

```kotlin
fun log(msg: String) = println("[${Thread.currentThread().name}] $msg")

fun main(args: Array<String>) {
    newSingleThreadContext("Ctx1").use { ctx1 ->
        newSingleThreadContext("Ctx2").use { ctx2 ->
            runBlocking(ctx1) {
                log("Started in ctx1")
                withContext(ctx2) {
                    log("Working in ctx2")
                }
                log("Back to ctx1")
            }
        }
    }
}
```

> You can get full code [here](core/kotlinx-coroutines-core/src/test/kotlin/guide/example-context-04.kt)

It demonstrates several new techniques. One is using [runBlocking] with an explicitly specified context, and
the other one is using [withContext] function to change a context of a coroutine while still staying in the
same coroutine as you can see in the output below:

```text
[Ctx1 @coroutine#1] Started in ctx1
[Ctx2 @coroutine#1] Working in ctx2
[Ctx1 @coroutine#1] Back to ctx1
```

<!--- TEST -->


Note, that is example also uses `use` function from the Kotlin standard library to release threads that
are created with [newSingleThreadContext] when they are no longer needed. 

### Job in the context

The coroutine's [Job] is part of its context. The coroutine can retrieve it from its own context 
using `coroutineContext[Job]` expression:

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    println("My job is ${coroutineContext[Job]}")
}
```

> You can get full code [here](core/kotlinx-coroutines-core/src/test/kotlin/guide/example-context-05.kt)

It produces something like that when running in [debug mode](#debugging-coroutines-and-threads):

```
My job is "coroutine#1":BlockingCoroutine{Active}@6d311334
```

<!--- TEST lines.size == 1 && lines[0].startsWith("My job is \"coroutine#1\":BlockingCoroutine{Active}@") -->

So, [isActive][CoroutineScope.isActive] in [CoroutineScope] is just a convenient shortcut for
`coroutineContext[Job]!!.isActive`.

### Children of a coroutine

When [coroutineContext][CoroutineScope.coroutineContext] of a coroutine is used to launch another coroutine,
the [Job] of the new coroutine becomes
a _child_ of the parent coroutine's job. When the parent coroutine is cancelled, all its children
are recursively cancelled, too. 
  
```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    // launch a coroutine to process some kind of incoming request
    val request = launch {
        // it spawns two other jobs, one with its separate context
        val job1 = launch {
            println("job1: I have my own context and execute independently!")
            delay(1000)
            println("job1: I am not affected by cancellation of the request")
        }
        // and the other inherits the parent context
        val job2 = launch(coroutineContext) {
            delay(100)
            println("job2: I am a child of the request coroutine")
            delay(1000)
            println("job2: I will not execute this line if my parent request is cancelled")
        }
        // request completes when both its sub-jobs complete:
        job1.join()
        job2.join()
    }
    delay(500)
    request.cancel() // cancel processing of the request
    delay(1000) // delay a second to see what happens
    println("main: Who has survived request cancellation?")
}
```

> You can get full code [here](core/kotlinx-coroutines-core/src/test/kotlin/guide/example-context-06.kt)

The output of this code is:

```text
job1: I have my own context and execute independently!
job2: I am a child of the request coroutine
job1: I am not affected by cancellation of the request
main: Who has survived request cancellation?
```

<!--- TEST -->

### Combining contexts

Coroutine contexts can be combined using `+` operator. The context on the right-hand side replaces relevant entries
of the context on the left-hand side. For example, a [Job] of the parent coroutine can be inherited, while 
its dispatcher replaced:

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    // start a coroutine to process some kind of incoming request
    val request = launch(coroutineContext) { // use the context of `runBlocking`
        // spawns CPU-intensive child job in CommonPool !!! 
        val job = launch(coroutineContext + CommonPool) {
            println("job: I am a child of the request coroutine, but with a different dispatcher")
            delay(1000)
            println("job: I will not execute this line if my parent request is cancelled")
        }
        job.join() // request completes when its sub-job completes
    }
    delay(500)
    request.cancel() // cancel processing of the request
    delay(1000) // delay a second to see what happens
    println("main: Who has survived request cancellation?")
}
```

> You can get full code [here](core/kotlinx-coroutines-core/src/test/kotlin/guide/example-context-07.kt)

The expected outcome of this code is: 

```text
job: I am a child of the request coroutine, but with a different dispatcher
main: Who has survived request cancellation?
```

<!--- TEST -->

### Parental responsibilities 

A parent coroutine always waits for completion of all its children. Parent does not have to explicitly track
all the children it launches and it does not have to use [Job.join] to wait for them at the end:

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    // launch a coroutine to process some kind of incoming request
    val request = launch {
        repeat(3) { i -> // launch a few children jobs
            launch(coroutineContext)  {
                delay((i + 1) * 200L) // variable delay 200ms, 400ms, 600ms
                println("Coroutine $i is done")
            }
        }
        println("request: I'm done and I don't explicitly join my children that are still active")
    }
    request.join() // wait for completion of the request, including all its children
    println("Now processing of the request is complete")
}
```

> You can get full code [here](core/kotlinx-coroutines-core/src/test/kotlin/guide/example-context-08.kt)

The result is going to be:

```text
request: I'm done and I don't explicitly join my children that are still active
Coroutine 0 is done
Coroutine 1 is done
Coroutine 2 is done
Now processing of the request is complete
```

<!--- TEST -->

### Naming coroutines for debugging

Automatically assigned ids are good when coroutines log often and you just need to correlate log records
coming from the same coroutine. However, when coroutine is tied to the processing of a specific request
or doing some specific background task, it is better to name it explicitly for debugging purposes.
[CoroutineName] context element serves the same function as a thread name. It'll get displayed in the thread name that
is executing this coroutine when [debugging mode](#debugging-coroutines-and-threads) is turned on.

The following example demonstrates this concept:

```kotlin
fun log(msg: String) = println("[${Thread.currentThread().name}] $msg")

fun main(args: Array<String>) = runBlocking(CoroutineName("main")) {
    log("Started main coroutine")
    // run two background value computations
    val v1 = async(CoroutineName("v1coroutine")) {
        delay(500)
        log("Computing v1")
        252
    }
    val v2 = async(CoroutineName("v2coroutine")) {
        delay(1000)
        log("Computing v2")
        6
    }
    log("The answer for v1 / v2 = ${v1.await() / v2.await()}")
}
```

> You can get full code [here](core/kotlinx-coroutines-core/src/test/kotlin/guide/example-context-09.kt)

The output it produces with `-Dkotlinx.coroutines.debug` JVM option is similar to:
 
```text
[main @main#1] Started main coroutine
[ForkJoinPool.commonPool-worker-1 @v1coroutine#2] Computing v1
[ForkJoinPool.commonPool-worker-2 @v2coroutine#3] Computing v2
[main @main#1] The answer for v1 / v2 = 42
```

<!--- TEST FLEXIBLE_THREAD -->

### Cancellation via explicit job

Let us put our knowledge about contexts, children and jobs together. Assume that our application has
an object with a lifecycle, but that object is not a coroutine. For example, we are writing an Android application
and launch various coroutines in the context of an Android activity to perform asynchronous operations to fetch 
and update data, do animations, etc. All of these coroutines must be cancelled when activity is destroyed
to avoid memory leaks. 
  
We can manage a lifecycle of our coroutines by creating an instance of [Job] that is tied to 
the lifecycle of our activity. A job instance is created using [Job()] factory function
as the following example shows. For convenience, rather than using `launch(coroutineContext + job)` expression,
we can write `launch(coroutineContext, parent = job)` to make explicit the fact that the parent job is being used.

Now, a single invocation of [Job.cancel] cancels all the children we've launched. 
Moreover, [Job.join] waits for all of them to complete, so we can also use [cancelAndJoin] here in
this example:

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    val job = Job() // create a job object to manage our lifecycle
    // now launch ten coroutines for a demo, each working for a different time
    val coroutines = List(10) { i ->
        // they are all children of our job object
        launch(coroutineContext, parent = job) { // we use the context of main runBlocking thread, but with our parent job
            delay((i + 1) * 200L) // variable delay 200ms, 400ms, ... etc
            println("Coroutine $i is done")
        }
    }
    println("Launched ${coroutines.size} coroutines")
    delay(500L) // delay for half a second
    println("Cancelling the job!")
    job.cancelAndJoin() // cancel all our coroutines and wait for all of them to complete
}
```

> You can get full code [here](core/kotlinx-coroutines-core/src/test/kotlin/guide/example-context-10.kt)

The output of this example is:

```text
Launched 10 coroutines
Coroutine 0 is done
Coroutine 1 is done
Cancelling the job!
```

<!--- TEST -->

As you can see, only the first three coroutines had printed a message and the others were cancelled 
by a single  invocation of `job.cancelAndJoin()`. So all we need to do in our hypothetical Android 
application is to create a parent job object when activity is created, use it for child coroutines,
and cancel it when activity is destroyed. We cannot `join` them in the case of Android lifecycle, 
since it is synchronous, but this joining ability is useful when building backend services to ensure bounded 
resource usage.

## Channels

Deferred values provide a convenient way to transfer a single value between coroutines.
Channels provide a way to transfer a stream of values.

<!--- INCLUDE .*/example-channel-([0-9]+).kt
import kotlinx.coroutines.experimental.channels.*
-->

### Channel basics

A [Channel] is conceptually very similar to `BlockingQueue`. One key difference is that
instead of a blocking `put` operation it has a suspending [send][SendChannel.send], and instead of 
a blocking `take` operation it has a suspending [receive][ReceiveChannel.receive].

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    val channel = Channel<Int>()
    launch {
        // this might be heavy CPU-consuming computation or async logic, we'll just send five squares
        for (x in 1..5) channel.send(x * x)
    }
    // here we print five received integers:
    repeat(5) { println(channel.receive()) }
    println("Done!")
}
```

> You can get full code [here](core/kotlinx-coroutines-core/src/test/kotlin/guide/example-channel-01.kt)

The output of this code is:

```text
1
4
9
16
25
Done!
```

<!--- TEST -->

### Closing and iteration over channels 

Unlike a queue, a channel can be closed to indicate that no more elements are coming. 
On the receiver side it is convenient to use a regular `for` loop to receive elements 
from the channel. 
 
Conceptually, a [close][SendChannel.close] is like sending a special close token to the channel. 
The iteration stops as soon as this close token is received, so there is a guarantee 
that all previously sent elements before the close are received:

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    val channel = Channel<Int>()
    launch {
        for (x in 1..5) channel.send(x * x)
        channel.close() // we're done sending
    }
    // here we print received values using `for` loop (until the channel is closed)
    for (y in channel) println(y)
    println("Done!")
}
```

> You can get full code [here](core/kotlinx-coroutines-core/src/test/kotlin/guide/example-channel-02.kt)

<!--- TEST 
1
4
9
16
25
Done!
-->

### Building channel producers

The pattern where a coroutine is producing a sequence of elements is quite common. 
This is a part of _producer-consumer_ pattern that is often found in concurrent code. 
You could abstract such a producer into a function that takes channel as its parameter, but this goes contrary
to common sense that results must be returned from functions. 

There is a convenience coroutine builder named [produce] that makes it easy to do it right on producer side,
and an extension function [consumeEach], that replaces a `for` loop on the consumer side:

```kotlin
fun produceSquares() = produce<Int> {
    for (x in 1..5) send(x * x)
}

fun main(args: Array<String>) = runBlocking<Unit> {
    val squares = produceSquares()
    squares.consumeEach { println(it) }
    println("Done!")
}
```

> You can get full code [here](core/kotlinx-coroutines-core/src/test/kotlin/guide/example-channel-03.kt)

<!--- TEST 
1
4
9
16
25
Done!
-->

### Pipelines

A pipeline is a pattern where one coroutine is producing, possibly infinite, stream of values:

```kotlin
fun produceNumbers() = produce<Int> {
    var x = 1
    while (true) send(x++) // infinite stream of integers starting from 1
}
```

And another coroutine or coroutines are consuming that stream, doing some processing, and producing some other results.
In the below example the numbers are just squared:

```kotlin
fun square(numbers: ReceiveChannel<Int>) = produce<Int> {
    for (x in numbers) send(x * x)
}
```

The main code starts and connects the whole pipeline:

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    val numbers = produceNumbers() // produces integers from 1 and on
    val squares = square(numbers) // squares integers
    for (i in 1..5) println(squares.receive()) // print first five
    println("Done!") // we are done
    squares.cancel() // need to cancel these coroutines in a larger app
    numbers.cancel()
}
```

> You can get full code [here](core/kotlinx-coroutines-core/src/test/kotlin/guide/example-channel-04.kt)

<!--- TEST 
1
4
9
16
25
Done!
-->

We don't have to cancel these coroutines in this example app, because
[coroutines are like daemon threads](#coroutines-are-like-daemon-threads), 
but in a larger app we'll need to stop our pipeline if we don't need it anymore.
Alternatively, we could have run pipeline coroutines as 
[children of a main coroutine](#children-of-a-coroutine) as is demonstrated in the following example.

### Prime numbers with pipeline

Let's take pipelines to the extreme with an example that generates prime numbers using a pipeline 
of coroutines. We start with an infinite sequence of numbers. This time we introduce an 
explicit `context` parameter and pass it to [produce] builder, 
so that caller can control where our coroutines run:
 
<!--- INCLUDE core/kotlinx-coroutines-core/src/test/kotlin/guide/example-channel-05.kt  
import kotlin.coroutines.experimental.CoroutineContext
-->
 
```kotlin
fun numbersFrom(context: CoroutineContext, start: Int) = produce<Int>(context) {
    var x = start
    while (true) send(x++) // infinite stream of integers from start
}
```

The following pipeline stage filters an incoming stream of numbers, removing all the numbers 
that are divisible by the given prime number:

```kotlin
fun filter(context: CoroutineContext, numbers: ReceiveChannel<Int>, prime: Int) = produce<Int>(context) {
    for (x in numbers) if (x % prime != 0) send(x)
}
```

Now we build our pipeline by starting a stream of numbers from 2, taking a prime number from the current channel, 
and launching new pipeline stage for each prime number found:
 
```
numbersFrom(2) -> filter(2) -> filter(3) -> filter(5) -> filter(7) ... 
``` 
 
The following example prints the first ten prime numbers, 
running the whole pipeline in the context of the main thread. Since all the coroutines are launched as
children of the main [runBlocking] coroutine in its [coroutineContext][CoroutineScope.coroutineContext],
we don't have to keep an explicit list of all the coroutine we have started. 
We use [cancelChildren][kotlin.coroutines.experimental.CoroutineContext.cancelChildren] 
extension function to cancel all the children coroutines. 

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    var cur = numbersFrom(coroutineContext, 2)
    for (i in 1..10) {
        val prime = cur.receive()
        println(prime)
        cur = filter(coroutineContext, cur, prime)
    }
    coroutineContext.cancelChildren() // cancel all children to let main finish
}
```

> You can get full code [here](core/kotlinx-coroutines-core/src/test/kotlin/guide/example-channel-05.kt)

The output of this code is:

```text
2
3
5
7
11
13
17
19
23
29
```

<!--- TEST -->

Note, that you can build the same pipeline using 
[`buildIterator`](https://kotlinlang.org/api/latest/jvm/stdlib/kotlin.coroutines.experimental/build-iterator.html) 
coroutine builder from the standard library. 
Replace `produce` with `buildIterator`, `send` with `yield`, `receive` with `next`, 
`ReceiveChannel` with `Iterator`, and get rid of the context. You will not need `runBlocking` either.
However, the benefit of a pipeline that uses channels as shown above is that it can actually use 
multiple CPU cores if you run it in [CommonPool] context.

Anyway, this is an extremely impractical way to find prime numbers. In practice, pipelines do involve some
other suspending invocations (like asynchronous calls to remote services) and these pipelines cannot be
built using `buildSeqeunce`/`buildIterator`, because they do not allow arbitrary suspension, unlike
`produce`, which is fully asynchronous.
 
### Fan-out

Multiple coroutines may receive from the same channel, distributing work between themselves.
Let us start with a producer coroutine that is periodically producing integers 
(ten numbers per second):

```kotlin
fun produceNumbers() = produce<Int> {
    var x = 1 // start from 1
    while (true) {
        send(x++) // produce next
        delay(100) // wait 0.1s
    }
}
```

Then we can have several processor coroutines. In this example, they just print their id and
received number:

```kotlin
fun launchProcessor(id: Int, channel: ReceiveChannel<Int>) = launch {
    channel.consumeEach {
        println("Processor #$id received $it")
    }    
}
```

Now let us launch five processors and let them work for almost a second. See what happens:

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    val producer = produceNumbers()
    repeat(5) { launchProcessor(it, producer) }
    delay(950)
    producer.cancel() // cancel producer coroutine and thus kill them all
}
```

> You can get full code [here](core/kotlinx-coroutines-core/src/test/kotlin/guide/example-channel-06.kt)

The output will be similar to the the following one, albeit the processor ids that receive
each specific integer may be different:

```
Processor #2 received 1
Processor #4 received 2
Processor #0 received 3
Processor #1 received 4
Processor #3 received 5
Processor #2 received 6
Processor #4 received 7
Processor #0 received 8
Processor #1 received 9
Processor #3 received 10
```

<!--- TEST lines.size == 10 && lines.withIndex().all { (i, line) -> line.startsWith("Processor #") && line.endsWith(" received ${i + 1}") } -->

Note, that cancelling a producer coroutine closes its channel, thus eventually terminating iteration
over the channel that processor coroutines are doing.

### Fan-in

Multiple coroutines may send to the same channel.
For example, let us have a channel of strings, and a suspending function that 
repeatedly sends a specified string to this channel with a specified delay:

```kotlin
suspend fun sendString(channel: SendChannel<String>, s: String, time: Long) {
    while (true) {
        delay(time)
        channel.send(s)
    }
}
```

Now, let us see what happens if we launch a couple of coroutines sending strings 
(in this example we launch them in the context of the main thread as main coroutine's children):

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    val channel = Channel<String>()
    launch(coroutineContext) { sendString(channel, "foo", 200L) }
    launch(coroutineContext) { sendString(channel, "BAR!", 500L) }
    repeat(6) { // receive first six
        println(channel.receive())
    }
    coroutineContext.cancelChildren() // cancel all children to let main finish
}
```

> You can get full code [here](core/kotlinx-coroutines-core/src/test/kotlin/guide/example-channel-07.kt)

The output is:

```text
foo
foo
BAR!
foo
foo
BAR!
```

<!--- TEST -->

### Buffered channels

The channels shown so far had no buffer. Unbuffered channels transfer elements when sender and receiver 
meet each other (aka rendezvous). If send is invoked first, then it is suspended until receive is invoked, 
if receive is invoked first, it is suspended until send is invoked.

Both [Channel()] factory function and [produce] builder take an optional `capacity` parameter to
specify _buffer size_. Buffer allows senders to send multiple elements before suspending, 
similar to the `BlockingQueue` with a specified capacity, which blocks when buffer is full.

Take a look at the behavior of the following code:

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    val channel = Channel<Int>(4) // create buffered channel
    val sender = launch(coroutineContext) { // launch sender coroutine
        repeat(10) {
            println("Sending $it") // print before sending each element
            channel.send(it) // will suspend when buffer is full
        }
    }
    // don't receive anything... just wait....
    delay(1000)
    sender.cancel() // cancel sender coroutine
}
```

> You can get full code [here](core/kotlinx-coroutines-core/src/test/kotlin/guide/example-channel-08.kt)

It prints "sending" _five_ times using a buffered channel with capacity of _four_:

```text
Sending 0
Sending 1
Sending 2
Sending 3
Sending 4
```

<!--- TEST -->

The first four elements are added to the buffer and the sender suspends when trying to send the fifth one.

### Channels are fair

Send and receive operations to channels are _fair_ with respect to the order of their invocation from 
multiple coroutines. They are served in first-in first-out order, e.g. the first coroutine to invoke `receive` 
gets the element. In the following example two coroutines "ping" and "pong" are 
receiving the "ball" object from the shared "table" channel. 

```kotlin
data class Ball(var hits: Int)

fun main(args: Array<String>) = runBlocking<Unit> {
    val table = Channel<Ball>() // a shared table
    launch(coroutineContext) { player("ping", table) }
    launch(coroutineContext) { player("pong", table) }
    table.send(Ball(0)) // serve the ball
    delay(1000) // delay 1 second
    coroutineContext.cancelChildren() // game over, cancel them
}

suspend fun player(name: String, table: Channel<Ball>) {
    for (ball in table) { // receive the ball in a loop
        ball.hits++
        println("$name $ball")
        delay(300) // wait a bit
        table.send(ball) // send the ball back
    }
}
```

> You can get full code [here](core/kotlinx-coroutines-core/src/test/kotlin/guide/example-channel-09.kt)

The "ping" coroutine is started first, so it is the first one to receive the ball. Even though "ping"
coroutine immediately starts receiving the ball again after sending it back to the table, the ball gets
received by the "pong" coroutine, because it was already waiting for it:

```text
ping Ball(hits=1)
pong Ball(hits=2)
ping Ball(hits=3)
pong Ball(hits=4)
```

<!--- TEST -->

Note, that sometimes channels may produce executions that look unfair due to the nature of the executor
that is being used. See [this issue](https://github.com/Kotlin/kotlinx.coroutines/issues/111) for details.

## Shared mutable state and concurrency

Coroutines can be executed concurrently using a multi-threaded dispatcher like the default [CommonPool]. It presents
all the usual concurrency problems. The main problem being synchronization of access to **shared mutable state**. 
Some solutions to this problem in the land of coroutines are similar to the solutions in the multi-threaded world, 
but others are unique.

### The problem

Let us launch a thousand coroutines all doing the same action thousand times (for a total of a million executions). 
We'll also measure their completion time for further comparisons:

<!--- INCLUDE .*/example-sync-([0-9a-z]+).kt
import kotlin.coroutines.experimental.CoroutineContext
import kotlin.system.measureTimeMillis
-->

<!--- INCLUDE .*/example-sync-03.kt
import java.util.concurrent.atomic.AtomicInteger
-->

<!--- INCLUDE .*/example-sync-06.kt
import kotlinx.coroutines.experimental.sync.Mutex
import kotlinx.coroutines.experimental.sync.withLock
-->

<!--- INCLUDE .*/example-sync-07.kt
import kotlinx.coroutines.experimental.channels.*
-->

```kotlin
suspend fun massiveRun(context: CoroutineContext, action: suspend () -> Unit) {
    val n = 1000 // number of coroutines to launch
    val k = 1000 // times an action is repeated by each coroutine
    val time = measureTimeMillis {
        val jobs = List(n) {
            launch(context) {
                repeat(k) { action() }
            }
        }
        jobs.forEach { it.join() }
    }
    println("Completed ${n * k} actions in $time ms")    
}
```

<!--- INCLUDE .*/example-sync-([0-9a-z]+).kt -->

We start with a very simple action that increments a shared mutable variable using 
multi-threaded [CommonPool] context. 

```kotlin
var counter = 0

fun main(args: Array<String>) = runBlocking<Unit> {
    massiveRun(CommonPool) {
        counter++
    }
    println("Counter = $counter")
}
```

> You can get full code [here](core/kotlinx-coroutines-core/src/test/kotlin/guide/example-sync-01.kt)

<!--- TEST LINES_START
Completed 1000000 actions in
Counter =
-->

What does it print at the end? It is highly unlikely to ever print "Counter = 1000000", because a thousand coroutines 
increment the `counter` concurrently from multiple threads without any synchronization.

> Note: if you have an old system with 2 or fewer CPUs, then you _will_ consistently see 1000000, because
`CommonPool` is running in only one thread in this case. To reproduce the problem you'll need to make the
following change:

```kotlin
val mtContext = newFixedThreadPoolContext(2, "mtPool") // explicitly define context with two threads
var counter = 0

fun main(args: Array<String>) = runBlocking<Unit> {
    massiveRun(mtContext) { // use it instead of CommonPool in this sample and below 
        counter++
    }
    println("Counter = $counter")
}
```

> You can get full code [here](core/kotlinx-coroutines-core/src/test/kotlin/guide/example-sync-01b.kt)

<!--- TEST LINES_START
Completed 1000000 actions in
Counter =
-->

### Volatiles are of no help

There is common misconception that making a variable `volatile` solves concurrency problem. Let us try it:

```kotlin
@Volatile // in Kotlin `volatile` is an annotation 
var counter = 0

fun main(args: Array<String>) = runBlocking<Unit> {
    massiveRun(CommonPool) {
        counter++
    }
    println("Counter = $counter")
}
```

> You can get full code [here](core/kotlinx-coroutines-core/src/test/kotlin/guide/example-sync-02.kt)

<!--- TEST LINES_START
Completed 1000000 actions in
Counter =
-->

This code works slower, but we still don't get "Counter = 1000000" at the end, because volatile variables guarantee
linearizable (this is a technical term for "atomic") reads and writes to the corresponding variable, but
do not provide atomicity of larger actions (increment in our case).

### Thread-safe data structures

The general solution that works both for threads and for coroutines is to use a thread-safe (aka synchronized,
linearizable, or atomic) data structure that provides all the necessarily synchronization for the corresponding 
operations that needs to be performed on a shared state. 
In the case of a simple counter we can use `AtomicInteger` class which has atomic `incrementAndGet` operations:

```kotlin
var counter = AtomicInteger()

fun main(args: Array<String>) = runBlocking<Unit> {
    massiveRun(CommonPool) {
        counter.incrementAndGet()
    }
    println("Counter = ${counter.get()}")
}
```

> You can get full code [here](core/kotlinx-coroutines-core/src/test/kotlin/guide/example-sync-03.kt)

<!--- TEST ARBITRARY_TIME
Completed 1000000 actions in xxx ms
Counter = 1000000
-->

This is the fastest solution for this particular problem. It works for plain counters, collections, queues and other
standard data structures and basic operations on them. However, it does not easily scale to complex
state or to complex operations that do not have ready-to-use thread-safe implementations. 

### Thread confinement fine-grained

_Thread confinement_ is an approach to the problem of shared mutable state where all access to the particular shared
state is confined to a single thread. It is typically used in UI applications, where all UI state is confined to 
the single event-dispatch/application thread. It is easy to apply with coroutines by using a  
single-threaded context:

```kotlin
val counterContext = newSingleThreadContext("CounterContext")
var counter = 0

fun main(args: Array<String>) = runBlocking<Unit> {
    massiveRun(CommonPool) { // run each coroutine in CommonPool
        withContext(counterContext) { // but confine each increment to the single-threaded context
            counter++
        }
    }
    println("Counter = $counter")
}
```

> You can get full code [here](core/kotlinx-coroutines-core/src/test/kotlin/guide/example-sync-04.kt)

<!--- TEST ARBITRARY_TIME
Completed 1000000 actions in xxx ms
Counter = 1000000
-->

This code works very slowly, because it does _fine-grained_ thread-confinement. Each individual increment switches 
from multi-threaded `CommonPool` context to the single-threaded context using [withContext] block.

### Thread confinement coarse-grained

In practice, thread confinement is performed in large chunks, e.g. big pieces of state-updating business logic
are confined to the single thread. The following example does it like that, running each coroutine in 
the single-threaded context to start with.

```kotlin
val counterContext = newSingleThreadContext("CounterContext")
var counter = 0

fun main(args: Array<String>) = runBlocking<Unit> {
    massiveRun(counterContext) { // run each coroutine in the single-threaded context
        counter++
    }
    println("Counter = $counter")
}
```

> You can get full code [here](core/kotlinx-coroutines-core/src/test/kotlin/guide/example-sync-05.kt)

<!--- TEST ARBITRARY_TIME
Completed 1000000 actions in xxx ms
Counter = 1000000
-->

This now works much faster and produces correct result.

### Mutual exclusion

Mutual exclusion solution to the problem is to protect all modifications of the shared state with a _critical section_
that is never executed concurrently. In a blocking world you'd typically use `synchronized` or `ReentrantLock` for that.
Coroutine's alternative is called [Mutex]. It has [lock][Mutex.lock] and [unlock][Mutex.unlock] functions to 
delimit a critical section. The key difference is that `Mutex.lock` is a suspending function. It does not block a thread.

There is also [withLock] extension function that conveniently represents 
`mutex.lock(); try { ... } finally { mutex.unlock() }` pattern: 

```kotlin
val mutex = Mutex()
var counter = 0

fun main(args: Array<String>) = runBlocking<Unit> {
    massiveRun(CommonPool) {
        mutex.withLock {
            counter++        
        }
    }
    println("Counter = $counter")
}
```

> You can get full code [here](core/kotlinx-coroutines-core/src/test/kotlin/guide/example-sync-06.kt)

<!--- TEST ARBITRARY_TIME
Completed 1000000 actions in xxx ms
Counter = 1000000
-->

The locking in this example is fine-grained, so it pays the price. However, it is a good choice for some situations
where you absolutely must modify some shared state periodically, but there is no natural thread that this state
is confined to.

### Actors

An actor is a combination of a coroutine, the state that is confined and is encapsulated into this coroutine,
and a channel to communicate with other coroutines. A simple actor can be written as a function, 
but an actor with a complex state is better suited for a class. 

There is an [actor] coroutine builder that conveniently combines actor's mailbox channel into its 
scope to receive messages from and combines the send channel into the resulting job object, so that a 
single reference to the actor can be carried around as its handle.

The first step of using an actor is to define a class of messages that an actor is going to process.
Kotlin's [sealed classes](https://kotlinlang.org/docs/reference/sealed-classes.html) are well suited for that purpose.
We define `CounterMsg` sealed class with `IncCounter` message to increment a counter and `GetCounter` message
to get its value. The later needs to send a response. A [CompletableDeferred] communication
primitive, that represents a single value that will be known (communicated) in the future,
is used here for that purpose.

```kotlin
// Message types for counterActor
sealed class CounterMsg
object IncCounter : CounterMsg() // one-way message to increment counter
class GetCounter(val response: CompletableDeferred<Int>) : CounterMsg() // a request with reply
```

Then we define a function that launches an actor using an [actor] coroutine builder:

```kotlin
// This function launches a new counter actor
fun counterActor() = actor<CounterMsg> {
    var counter = 0 // actor state
    for (msg in channel) { // iterate over incoming messages
        when (msg) {
            is IncCounter -> counter++
            is GetCounter -> msg.response.complete(counter)
        }
    }
}
```

The main code is straightforward:

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    val counter = counterActor() // create the actor
    massiveRun(CommonPool) {
        counter.send(IncCounter)
    }
    // send a message to get a counter value from an actor
    val response = CompletableDeferred<Int>()
    counter.send(GetCounter(response))
    println("Counter = ${response.await()}")
    counter.close() // shutdown the actor
}
```

> You can get full code [here](core/kotlinx-coroutines-core/src/test/kotlin/guide/example-sync-07.kt)

<!--- TEST ARBITRARY_TIME
Completed 1000000 actions in xxx ms
Counter = 1000000
-->

It does not matter (for correctness) what context the actor itself is executed in. An actor is
a coroutine and a coroutine is executed sequentially, so confinement of the state to the specific coroutine
works as a solution to the problem of shared mutable state.

Actor is more efficient than locking under load, because in this case it always has work to do and it does not 
have to switch to a different context at all.

> Note, that an [actor] coroutine builder is a dual of [produce] coroutine builder. An actor is associated 
  with the channel that it receives messages from, while a producer is associated with the channel that it 
  sends elements to.

## Select expression

Select expression makes it possible to await multiple suspending functions simultaneously and _select_
the first one that becomes available.

<!--- INCLUDE .*/example-select-([0-9]+).kt
import kotlinx.coroutines.experimental.channels.*
import kotlinx.coroutines.experimental.selects.*
-->

### Selecting from channels

Let us have two producers of strings: `fizz` and `buzz`. The `fizz` produces "Fizz" string every 300 ms:

<!--- INCLUDE .*/example-select-01.kt
import kotlin.coroutines.experimental.CoroutineContext
-->

```kotlin
fun fizz(context: CoroutineContext) = produce<String>(context) {
    while (true) { // sends "Fizz" every 300 ms
        delay(300)
        send("Fizz")
    }
}
```

And the `buzz` produces "Buzz!" string every 500 ms:

```kotlin
fun buzz(context: CoroutineContext) = produce<String>(context) {
    while (true) { // sends "Buzz!" every 500 ms
        delay(500)
        send("Buzz!")
    }
}
```

Using [receive][ReceiveChannel.receive] suspending function we can receive _either_ from one channel or the
other. But [select] expression allows us to receive from _both_ simultaneously using its
[onReceive][ReceiveChannel.onReceive] clauses:

```kotlin
suspend fun selectFizzBuzz(fizz: ReceiveChannel<String>, buzz: ReceiveChannel<String>) {
    select<Unit> { // <Unit> means that this select expression does not produce any result 
        fizz.onReceive { value ->  // this is the first select clause
            println("fizz -> '$value'")
        }
        buzz.onReceive { value ->  // this is the second select clause
            println("buzz -> '$value'")
        }
    }
}
```

Let us run it all seven times:

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    val fizz = fizz(coroutineContext)
    val buzz = buzz(coroutineContext)
    repeat(7) {
        selectFizzBuzz(fizz, buzz)
    }
    coroutineContext.cancelChildren() // cancel fizz & buzz coroutines    
}
```

> You can get full code [here](core/kotlinx-coroutines-core/src/test/kotlin/guide/example-select-01.kt)

The result of this code is: 

```text
fizz -> 'Fizz'
buzz -> 'Buzz!'
fizz -> 'Fizz'
fizz -> 'Fizz'
buzz -> 'Buzz!'
fizz -> 'Fizz'
buzz -> 'Buzz!'
```

<!--- TEST -->

### Selecting on close

The [onReceive][ReceiveChannel.onReceive] clause in `select` fails when the channel is closed and the corresponding
`select` throws an exception. We can use [onReceiveOrNull][ReceiveChannel.onReceiveOrNull] clause to perform a
specific action when the channel is closed. The following example also shows that `select` is an expression that returns 
the result of its selected clause:

```kotlin
suspend fun selectAorB(a: ReceiveChannel<String>, b: ReceiveChannel<String>): String =
    select<String> {
        a.onReceiveOrNull { value -> 
            if (value == null) 
                "Channel 'a' is closed" 
            else 
                "a -> '$value'"
        }
        b.onReceiveOrNull { value -> 
            if (value == null) 
                "Channel 'b' is closed"
            else    
                "b -> '$value'"
        }
    }
```

Let's use it with channel `a` that produces "Hello" string four times and 
channel `b` that produces "World" four times:

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    // we are using the context of the main thread in this example for predictability ... 
    val a = produce<String>(coroutineContext) {
        repeat(4) { send("Hello $it") }
    }
    val b = produce<String>(coroutineContext) {
        repeat(4) { send("World $it") }
    }
    repeat(8) { // print first eight results
        println(selectAorB(a, b))
    }
    coroutineContext.cancelChildren()    
}
```

> You can get full code [here](core/kotlinx-coroutines-core/src/test/kotlin/guide/example-select-02.kt)

The result of this code is quite interesting, so we'll analyze it in mode detail:

```text
a -> 'Hello 0'
a -> 'Hello 1'
b -> 'World 0'
a -> 'Hello 2'
a -> 'Hello 3'
b -> 'World 1'
Channel 'a' is closed
Channel 'a' is closed
```

<!--- TEST -->

There are couple of observations to make out of it. 

First of all, `select` is _biased_ to the first clause. When several clauses are selectable at the same time, 
the first one among them gets selected. Here, both channels are constantly producing strings, so `a` channel,
being the first clause in select, wins. However, because we are using unbuffered channel, the `a` gets suspended from
time to time on its [send][SendChannel.send] invocation and gives a chance for `b` to send, too.

The second observation, is that [onReceiveOrNull][ReceiveChannel.onReceiveOrNull] gets immediately selected when the 
channel is already closed.

### Selecting to send

Select expression has [onSend][SendChannel.onSend] clause that can be used for a great good in combination 
with a biased nature of selection.

Let us write an example of producer of integers that sends its values to a `side` channel when 
the consumers on its primary channel cannot keep up with it:

<!--- INCLUDE
import kotlin.coroutines.experimental.CoroutineContext
-->

```kotlin
fun produceNumbers(context: CoroutineContext, side: SendChannel<Int>) = produce<Int>(context) {
    for (num in 1..10) { // produce 10 numbers from 1 to 10
        delay(100) // every 100 ms
        select<Unit> {
            onSend(num) {} // Send to the primary channel
            side.onSend(num) {} // or to the side channel     
        }
    }
}
```

Consumer is going to be quite slow, taking 250 ms to process each number:
 
```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    val side = Channel<Int>() // allocate side channel
    launch(coroutineContext) { // this is a very fast consumer for the side channel
        side.consumeEach { println("Side channel has $it") }
    }
    produceNumbers(coroutineContext, side).consumeEach { 
        println("Consuming $it")
        delay(250) // let us digest the consumed number properly, do not hurry
    }
    println("Done consuming")
    coroutineContext.cancelChildren()    
}
``` 
 
> You can get full code [here](core/kotlinx-coroutines-core/src/test/kotlin/guide/example-select-03.kt)
  
So let us see what happens:
 
```text
Consuming 1
Side channel has 2
Side channel has 3
Consuming 4
Side channel has 5
Side channel has 6
Consuming 7
Side channel has 8
Side channel has 9
Consuming 10
Done consuming
```

<!--- TEST -->

### Selecting deferred values

Deferred values can be selected using [onAwait][Deferred.onAwait] clause. 
Let us start with an async function that returns a deferred string value after 
a random delay:

<!--- INCLUDE .*/example-select-04.kt
import java.util.*
-->

```kotlin
fun asyncString(time: Int) = async {
    delay(time.toLong())
    "Waited for $time ms"
}
```

Let us start a dozen of them with a random delay.

```kotlin
fun asyncStringsList(): List<Deferred<String>> {
    val random = Random(3)
    return List(12) { asyncString(random.nextInt(1000)) }
}
```

Now the main function awaits for the first of them to complete and counts the number of deferred values
that are still active. Note, that we've used here the fact that `select` expression is a Kotlin DSL, 
so we can provide clauses for it using an arbitrary code. In this case we iterate over a list
of deferred values to provide `onAwait` clause for each deferred value.

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    val list = asyncStringsList()
    val result = select<String> {
        list.withIndex().forEach { (index, deferred) ->
            deferred.onAwait { answer ->
                "Deferred $index produced answer '$answer'"
            }
        }
    }
    println(result)
    val countActive = list.count { it.isActive }
    println("$countActive coroutines are still active")
}
```

> You can get full code [here](core/kotlinx-coroutines-core/src/test/kotlin/guide/example-select-04.kt)

The output is:

```text
Deferred 4 produced answer 'Waited for 128 ms'
11 coroutines are still active
```

<!--- TEST -->

### Switch over a channel of deferred values

Let us write a channel producer function that consumes a channel of deferred string values, waits for each received
deferred value, but only until the next deferred value comes over or the channel is closed. This example puts together 
[onReceiveOrNull][ReceiveChannel.onReceiveOrNull] and [onAwait][Deferred.onAwait] clauses in the same `select`:

```kotlin
fun switchMapDeferreds(input: ReceiveChannel<Deferred<String>>) = produce<String> {
    var current = input.receive() // start with first received deferred value
    while (isActive) { // loop while not cancelled/closed
        val next = select<Deferred<String>?> { // return next deferred value from this select or null
            input.onReceiveOrNull { update ->
                update // replaces next value to wait
            }
            current.onAwait { value ->  
                send(value) // send value that current deferred has produced
                input.receiveOrNull() // and use the next deferred from the input channel
            }
        }
        if (next == null) {
            println("Channel was closed")
            break // out of loop
        } else {
            current = next
        }
    }
}
```

To test it, we'll use a simple async function that resolves to a specified string after a specified time:

```kotlin
fun asyncString(str: String, time: Long) = async {
    delay(time)
    str
}
```

The main function just launches a coroutine to print results of `switchMapDeferreds` and sends some test
data to it:

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    val chan = Channel<Deferred<String>>() // the channel for test
    launch(coroutineContext) { // launch printing coroutine
        for (s in switchMapDeferreds(chan)) 
            println(s) // print each received string
    }
    chan.send(asyncString("BEGIN", 100))
    delay(200) // enough time for "BEGIN" to be produced
    chan.send(asyncString("Slow", 500))
    delay(100) // not enough time to produce slow
    chan.send(asyncString("Replace", 100))
    delay(500) // give it time before the last one
    chan.send(asyncString("END", 500))
    delay(1000) // give it time to process
    chan.close() // close the channel ... 
    delay(500) // and wait some time to let it finish
}
```

> You can get full code [here](core/kotlinx-coroutines-core/src/test/kotlin/guide/example-select-05.kt)

The result of this code:

```text
BEGIN
Replace
END
Channel was closed
```

<!--- TEST -->

## Further reading

* [Guide to UI programming with coroutines](ui/coroutines-guide-ui.md)
* [Guide to reactive streams with coroutines](reactive/coroutines-guide-reactive.md)
* [Coroutines design document (KEEP)](https://github.com/Kotlin/kotlin-coroutines/blob/master/kotlin-coroutines-informal.md)
* [Full kotlinx.coroutines API reference](http://kotlin.github.io/kotlinx.coroutines)

<!--- MODULE kotlinx-coroutines-core -->
<!--- INDEX kotlinx.coroutines.experimental -->
[launch]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/launch.html
[delay]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/delay.html
[runBlocking]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/run-blocking.html
[Job]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-job/index.html
[cancelAndJoin]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/cancel-and-join.html
[Job.cancel]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-job/cancel.html
[Job.join]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-job/join.html
[CancellationException]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-cancellation-exception/index.html
[yield]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/yield.html
[CoroutineScope.isActive]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-coroutine-scope/is-active.html
[CoroutineScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-coroutine-scope/index.html
[withContext]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/with-context.html
[NonCancellable]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-non-cancellable/index.html
[withTimeout]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/with-timeout.html
[withTimeoutOrNull]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/with-timeout-or-null.html
[async]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/async.html
[Deferred]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-deferred/index.html
[CoroutineStart.LAZY]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-coroutine-start/-l-a-z-y.html
[Deferred.await]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-deferred/await.html
[Job.start]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-job/start.html
[CoroutineDispatcher]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-coroutine-dispatcher/index.html
[DefaultDispatcher]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-default-dispatcher.html
[CommonPool]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-common-pool/index.html
[CoroutineScope.coroutineContext]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-coroutine-scope/coroutine-context.html
[Unconfined]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-unconfined/index.html
[newSingleThreadContext]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/new-single-thread-context.html
[ThreadPoolDispatcher.close]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-thread-pool-dispatcher/close.html
[newCoroutineContext]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/new-coroutine-context.html
[CoroutineName]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-coroutine-name/index.html
[Job()]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-job.html
[kotlin.coroutines.experimental.CoroutineContext.cancelChildren]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/kotlin.coroutines.experimental.-coroutine-context/cancel-children.html
[CompletableDeferred]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-completable-deferred/index.html
[Deferred.onAwait]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-deferred/on-await.html
<!--- INDEX kotlinx.coroutines.experimental.sync -->
[Mutex]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.sync/-mutex/index.html
[Mutex.lock]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.sync/-mutex/lock.html
[Mutex.unlock]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.sync/-mutex/unlock.html
[withLock]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.sync/with-lock.html
<!--- INDEX kotlinx.coroutines.experimental.channels -->
[Channel]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.channels/-channel/index.html
[SendChannel.send]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.channels/-send-channel/send.html
[ReceiveChannel.receive]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.channels/-receive-channel/receive.html
[SendChannel.close]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.channels/-send-channel/close.html
[produce]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.channels/produce.html
[consumeEach]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.channels/consume-each.html
[Channel()]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.channels/-channel.html
[actor]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.channels/actor.html
[ReceiveChannel.onReceive]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.channels/-receive-channel/on-receive.html
[ReceiveChannel.onReceiveOrNull]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.channels/-receive-channel/on-receive-or-null.html
[SendChannel.onSend]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.channels/-send-channel/on-send.html
<!--- INDEX kotlinx.coroutines.experimental.selects -->
[select]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.selects/select.html
<!--- END -->
