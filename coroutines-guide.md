<!--- INCLUDE .*/example-([a-z]+)-([0-9]+)\.kt 
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
<!--- KNIT     kotlinx-coroutines-core/src/test/kotlin/guide/.*\.kt -->
<!--- TEST_OUT kotlinx-coroutines-core/src/test/kotlin/guide/test/GuideTest.kt
// This file was automatically generated from coroutines-guide.md by Knit tool. Do not edit.
package guide.test

import org.junit.Test

class GuideTest {
--> 

# Guide to kotlinx.coroutines by example

This is a short guide on core features of `kotlinx.coroutines` with a series of examples.

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
* [Shared mutable state and concurrency](#shared-mutable-state-and-concurrency)
  * [The problem](#the-problem)
  * [Thread-safe data structures](#thread-safe-data-structures)
  * [Thread confinement](#thread-confinement)
  * [Mutual exclusion](#mutual-exclusion)
  * [Actors](#actors)
* [Select expression](#select-expression)
  * [Selecting from channels](#selecting-from-channels)
  * [Selecting on close](#selecting-on-close)
  * [Selecting to send](#selecting-to-send)
  * [Selecting deferred values](#selecting-deferred-values)
  * [Switch over a channel of deferred values](#switch-over-a-channel-of-deferred-values)

<!--- END_TOC -->

## Coroutine basics

This section covers basic coroutine concepts.

### Your first coroutine

Run the following code:

```kotlin
fun main(args: Array<String>) {
    launch(CommonPool) { // create new coroutine in common thread pool
        delay(1000L) // non-blocking delay for 1 second (default time unit is ms)
        println("World!") // print after delay
    }
    println("Hello,") // main function continues while coroutine is delayed
    Thread.sleep(2000L) // block main thread for 2 seconds to keep JVM alive
}
```

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/guide/example-basic-01.kt)

Run this code:

```text
Hello,
World!
```

<!--- TEST -->

Essentially, coroutines are light-weight threads.
They are launched with [launch] _coroutine builder_.
You can achieve the same result replacing
`launch(CommonPool) { ... }` with `thread { ... }` and `delay(...)` with `Thread.sleep(...)`. Try it.

If you start by replacing `launch(CommonPool)` by `thread`, the compiler produces the following error:

```
Error: Kotlin: Suspend functions are only allowed to be called from a coroutine or another suspend function
```

That is because [delay] is a special _suspending function_ that does not block a thread, but _suspends_
coroutine and it can be only used from a coroutine.

### Bridging blocking and non-blocking worlds

The first example mixes _non-blocking_ `delay(...)` and _blocking_ `Thread.sleep(...)` in the same
code of `main` function. It is easy to get lost. Let's cleanly separate blocking and non-blocking
worlds by using [runBlocking]:

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> { // start main coroutine
    launch(CommonPool) { // create new coroutine in common thread pool
        delay(1000L)
        println("World!")
    }
    println("Hello,") // main coroutine continues while child is delayed
    delay(2000L) // non-blocking delay for 2 seconds to keep JVM alive
}
```

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/guide/example-basic-02.kt)

<!--- TEST
Hello,
World!
-->

The result is the same, but this code uses only non-blocking [delay]. 

`runBlocking { ... }` works as an adaptor that is used here to start the top-level main coroutine. 
The regular code outside of `runBlocking` _blocks_, until the coroutine inside `runBlocking` is active. 

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
    val job = launch(CommonPool) { // create new coroutine and keep a reference to its Job
        delay(1000L)
        println("World!")
    }
    println("Hello,")
    job.join() // wait until child coroutine completes
}
```

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/guide/example-basic-03.kt)

<!--- TEST
Hello,
World!
-->

Now the result is still the same, but the code of the main coroutine is not tied to the duration of
the background job in any way. Much better.

### Extract function refactoring

Let's extract the block of code inside `launch(CommonPool} { ... }` into a separate function. When you 
perform "Extract function" refactoring on this code you get a new function with `suspend` modifier.
That is your first _suspending function_. Suspending functions can be used inside coroutines
just like regular functions, but their additional feature is that they can, in turn, 
use other suspending functions, like `delay` in this example, to _suspend_ execution of a coroutine.

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    val job = launch(CommonPool) { doWorld() }
    println("Hello,")
    job.join()
}

// this is your first suspending function
suspend fun doWorld() {
    delay(1000L)
    println("World!")
}
```

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/guide/example-basic-04.kt)

<!--- TEST
Hello,
World!
-->

### Coroutines ARE light-weight

Run the following code:

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    val jobs = List(100_000) { // create a lot of coroutines and list their jobs
        launch(CommonPool) {
            delay(1000L)
            print(".")
        }
    }
    jobs.forEach { it.join() } // wait for all jobs to complete
}
```

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/guide/example-basic-05.kt)

<!--- TEST lines.size == 1 && lines[0] == ".".repeat(100_000) -->

It starts 100K coroutines and, after a second, each coroutine prints a dot. 
Now, try that with threads. What would happen? (Most likely your code will produce some sort of out-of-memory error)

### Coroutines are like daemon threads

The following code launches a long-running coroutine that prints "I'm sleeping" twice a second and then 
returns from the main function after some delay:

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    launch(CommonPool) {
        repeat(1000) { i ->
            println("I'm sleeping $i ...")
            delay(500L)
        }
    }
    delay(1300L) // just quit after delay
}
```

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/guide/example-basic-06.kt)

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
    val job = launch(CommonPool) {
        repeat(1000) { i ->
            println("I'm sleeping $i ...")
            delay(500L)
        }
    }
    delay(1300L) // delay a bit
    println("main: I'm tired of waiting!")
    job.cancel() // cancels the job
    delay(1300L) // delay a bit to ensure it was cancelled indeed
    println("main: Now I can quit.")
}
``` 

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/guide/example-cancel-01.kt)

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

### Cancellation is cooperative

Coroutine cancellation is _cooperative_. A coroutine code has to cooperate to be cancellable.
All the suspending functions in `kotlinx.coroutines` are _cancellable_. They check for cancellation of 
coroutine and throw [CancellationException] when cancelled. However, if a coroutine is working in 
a computation and does not check for cancellation, then it cannot be cancelled, like the following 
example shows:

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    val job = launch(CommonPool) {
        var nextPrintTime = 0L
        var i = 0
        while (i < 10) { // computation loop
            val currentTime = System.currentTimeMillis()
            if (currentTime >= nextPrintTime) {
                println("I'm sleeping ${i++} ...")
                nextPrintTime = currentTime + 500L
            }
        }
    }
    delay(1300L) // delay a bit
    println("main: I'm tired of waiting!")
    job.cancel() // cancels the job
    delay(1300L) // delay a bit to see if it was cancelled....
    println("main: Now I can quit.")
}
```

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/guide/example-cancel-02.kt)

Run it to see that it continues to print "I'm sleeping" even after cancellation.

<!--- TEST 
I'm sleeping 0 ...
I'm sleeping 1 ...
I'm sleeping 2 ...
main: I'm tired of waiting!
I'm sleeping 3 ...
I'm sleeping 4 ...
I'm sleeping 5 ...
main: Now I can quit.
-->

### Making computation code cancellable

There are two approaches to making computation code cancellable. The first one is to periodically 
invoke a suspending function. There is a [yield] function that is a good choice for that purpose.
The other one is to explicitly check the cancellation status. Let us try the later approach. 

Replace `while (true)` in the previous example with `while (isActive)` and rerun it. 

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    val job = launch(CommonPool) {
        var nextPrintTime = 0L
        var i = 0
        while (isActive) { // cancellable computation loop
            val currentTime = System.currentTimeMillis()
            if (currentTime >= nextPrintTime) {
                println("I'm sleeping ${i++} ...")
                nextPrintTime = currentTime + 500L
            }
        }
    }
    delay(1300L) // delay a bit
    println("main: I'm tired of waiting!")
    job.cancel() // cancels the job
    delay(1300L) // delay a bit to see if it was cancelled....
    println("main: Now I can quit.")
}
```

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/guide/example-cancel-03.kt)

As you can see, now this loop can be cancelled. [isActive][CoroutineScope.isActive] is a property that is available inside
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
all the usual way. For example, the `try {...} finally {...}` and Kotlin `use` function execute their
finalization actions normally when coroutine is cancelled:
 
```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    val job = launch(CommonPool) {
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
    job.cancel() // cancels the job
    delay(1300L) // delay a bit to ensure it was cancelled indeed
    println("main: Now I can quit.")
}
``` 

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/guide/example-cancel-04.kt)

The example above produces the following output:

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
`run(NonCancellable) {...}` using [run] function and [NonCancellable] context as the following example shows:
 
```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    val job = launch(CommonPool) {
        try {
            repeat(1000) { i ->
                println("I'm sleeping $i ...")
                delay(500L)
            }
        } finally {
            run(NonCancellable) {
                println("I'm running finally")
                delay(1000L)
                println("And I've just delayed for 1 sec because I'm non-cancellable")
            }
        }
    }
    delay(1300L) // delay a bit
    println("main: I'm tired of waiting!")
    job.cancel() // cancels the job
    delay(1300L) // delay a bit to ensure it was cancelled indeed
    println("main: Now I can quit.")
}
``` 

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/guide/example-cancel-05.kt)

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

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/guide/example-cancel-06.kt)

It produces the following output:

```text
I'm sleeping 0 ...
I'm sleeping 1 ...
I'm sleeping 2 ...
Exception in thread "main" java.util.concurrent.CancellationException: Timed out waiting for 1300 MILLISECONDS
```

<!--- TEST STARTS_WITH -->

We have not seen the [CancellationException] stack trace printed on the console before. That is because
inside a cancelled coroutine `CancellationException` is a considered a normal reason for coroutine completion. 
However, in this example we have used `withTimeout` right inside the `main` function. 

Because cancellation is just an exception, all the resources will be closed in a usual way. 
You can wrap the code with timeout in `try {...} catch (e: CancellationException) {...}` block if 
you need to do some additional action specifically on timeout.

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
In practise we do this if we use the results of the first function to make a decision on whether we need 
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

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/guide/example-compose-01.kt)

It produces something like this:

```text
The answer is 42
Completed in 2017 ms
```

<!--- TEST FLEXIBLE_TIME -->

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
        val one = async(CommonPool) { doSomethingUsefulOne() }
        val two = async(CommonPool) { doSomethingUsefulTwo() }
        println("The answer is ${one.await() + two.await()}")
    }
    println("Completed in $time ms")
}
```

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/guide/example-compose-02.kt)

It produces something like this:

```text
The answer is 42
Completed in 1017 ms
```

<!--- TEST FLEXIBLE_TIME -->

This is twice as fast, because we have concurrent execution of two coroutines. 
Note, that concurrency with coroutines is always explicit.

### Lazily started async

There is a laziness option to [async] with `start = false` parameter. 
It starts coroutine only when its result is needed by some 
[await][Deferred.await] or if a [start][Job.start] function 
is invoked. Run the following example that differs from the previous one only by this option:

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    val time = measureTimeMillis {
        val one = async(CommonPool, start = false) { doSomethingUsefulOne() }
        val two = async(CommonPool, start = false) { doSomethingUsefulTwo() }
        println("The answer is ${one.await() + two.await()}")
    }
    println("Completed in $time ms")
}
```

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/guide/example-compose-03.kt)

It produces something like this:

```text
The answer is 42
Completed in 2017 ms
```

<!--- TEST FLEXIBLE_TIME -->

So, we are back to sequential execution, because we _first_ start and await for `one`, _and then_ start and await
for `two`. It is not the intended use-case for laziness. It is designed as a replacement for
the standard `lazy` function in cases when computation of the value involves suspending functions.

### Async-style functions

We can define async-style functions that invoke `doSomethingUsefulOne` and `doSomethingUsefulTwo`
_asynchronously_ using [async] coroutine builder. It is a good style to name such functions with 
either "async" prefix of "Async" suffix to highlight the fact that they only start asynchronous 
computation and one needs to use the resulting deferred value to get the result.

```kotlin
// The result type of asyncSomethingUsefulOne is Deferred<Int>
fun asyncSomethingUsefulOne() = async(CommonPool) {
    doSomethingUsefulOne()
}

// The result type of asyncSomethingUsefulTwo is Deferred<Int>
fun asyncSomethingUsefulTwo() = async(CommonPool)  {
    doSomethingUsefulTwo()
}
```

Note, that these `asyncXXX` function are **not** _suspending_ functions. They can be used from anywhere.
However, their use always implies asynchronous (here meaning _concurrent_) execution of their action
with the invoking code.
 
The following example shows their use outside of coroutine:  
 
```kotlin
// note, that we don't have `runBlocking` to the right of `main` in this example
fun main(args: Array<String>) {
    val time = measureTimeMillis {
        // we can initiate async actions outside of a coroutine
        val one = asyncSomethingUsefulOne()
        val two = asyncSomethingUsefulTwo()
        // but waiting for a result must involve either suspending or blocking.
        // here we use `runBlocking { ... }` to block the main thread while waiting for the result
        runBlocking {
            println("The answer is ${one.await() + two.await()}")
        }
    }
    println("Completed in $time ms")
}
```

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/guide/example-compose-04.kt)

<!--- TEST FLEXIBLE_TIME
The answer is 42
Completed in 1085 ms
-->

## Coroutine context and dispatchers

We've already seen `launch(CommonPool) {...}`, `async(CommonPool) {...}`, `run(NonCancellable) {...}`, etc.
In these code snippets [CommonPool] and [NonCancellable] are _coroutine contexts_. 
This section covers other available choices.

### Dispatchers and threads

Coroutine context includes a [_coroutine dispatcher_][CoroutineDispatcher] which determines what thread or threads 
the corresponding coroutine uses for its execution. Coroutine dispatcher can confine coroutine execution 
to a specific thread, dispatch it to a thread pool, or let it run unconfined. Try the following example:

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    val jobs = arrayListOf<Job>()
    jobs += launch(Unconfined) { // not confined -- will work with main thread
        println(" 'Unconfined': I'm working in thread ${Thread.currentThread().name}")
    }
    jobs += launch(context) { // context of the parent, runBlocking coroutine
        println("    'context': I'm working in thread ${Thread.currentThread().name}")
    }
    jobs += launch(CommonPool) { // will get dispatched to ForkJoinPool.commonPool (or equivalent)
        println(" 'CommonPool': I'm working in thread ${Thread.currentThread().name}")
    }
    jobs += launch(newSingleThreadContext("MyOwnThread")) { // will get its own new thread
        println("     'newSTC': I'm working in thread ${Thread.currentThread().name}")
    }
    jobs.forEach { it.join() }
}
```

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/guide/example-context-01.kt)

It produces the following output (maybe in different order):

```text
 'Unconfined': I'm working in thread main
 'CommonPool': I'm working in thread ForkJoinPool.commonPool-worker-1
     'newSTC': I'm working in thread MyOwnThread
    'context': I'm working in thread main
```

<!--- TEST LINES_START_UNORDERED -->

The difference between parent [context][CoroutineScope.context] and [Unconfined] context will be shown later.

### Unconfined vs confined dispatcher
 
The [Unconfined] coroutine dispatcher starts coroutine in the caller thread, but only until the
first suspension point. After suspension it resumes in the thread that is fully determined by the
suspending function that was invoked. Unconfined dispatcher is appropriate when coroutine does not
consume CPU time nor updates any shared data (like UI) that is confined to a specific thread. 

On the other side, [context][CoroutineScope.context] property that is available inside the block of any coroutine 
via [CoroutineScope] interface, is a reference to a context of this particular coroutine. 
This way, a parent context can be inherited. The default context of [runBlocking], in particular,
is confined to be invoker thread, so inheriting it has the effect of confining execution to
this thread with a predictable FIFO scheduling.

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    val jobs = arrayListOf<Job>()
    jobs += launch(Unconfined) { // not confined -- will work with main thread
        println(" 'Unconfined': I'm working in thread ${Thread.currentThread().name}")
        delay(1000)
        println(" 'Unconfined': After delay in thread ${Thread.currentThread().name}")
    }
    jobs += launch(context) { // context of the parent, runBlocking coroutine
        println("    'context': I'm working in thread ${Thread.currentThread().name}")
        delay(1000)
        println("    'context': After delay in thread ${Thread.currentThread().name}")
    }
    jobs.forEach { it.join() }
}
```

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/guide/example-contest-02.kt)

Produces the output: 
 
```text
 'Unconfined': I'm working in thread main
    'context': I'm working in thread main
 'Unconfined': After delay in thread kotlinx.coroutines.ScheduledExecutor
    'context': After delay in thread main
```

<!--- TEST LINES_START -->
 
So, the coroutine the had inherited `context` of `runBlocking {...}` continues to execute in the `main` thread,
while the unconfined one had resumed in the scheduler thread that [delay] function is using.

### Debugging coroutines and threads

Coroutines can suspend on one thread and resume on another thread with [Unconfined] dispatcher or 
with a multi-threaded dispatcher like [CommonPool]. Even with a single-threaded dispatcher it might be hard to
figure out what coroutine was doing what, where, and when. The common approach to debugging applications with 
threads is to print the thread name in the log file on each log statement. This feature is universally supported
by logging frameworks. When using coroutines, the thread name alone does not give much of a context, so 
`kotlinx.coroutines` includes debugging facilities to make it easier. 

Run the following code with `-Dkotlinx.coroutines.debug` JVM option:

```kotlin
fun log(msg: String) = println("[${Thread.currentThread().name}] $msg")

fun main(args: Array<String>) = runBlocking<Unit> {
    val a = async(context) {
        log("I'm computing a piece of the answer")
        6
    }
    val b = async(context) {
        log("I'm computing another piece of the answer")
        7
    }
    log("The answer is ${a.await() * b.await()}")
}
```

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/guide/example-context-03.kt)

There are three coroutines. The main coroutine (#1) -- `runBlocking` one, 
and two coroutines computing deferred values `a` (#2) and `b` (#3).
They are all executing in the context of `runBlocking` and are confined to the main thread.
The output of this code is:

```text
[main @coroutine#2] I'm computing a piece of the answer
[main @coroutine#3] I'm computing another piece of the answer
[main @coroutine#1] The answer is 42
```

<!--- TEST -->

The `log` function prints the name of the thread in square brackets and you can see, that it is the `main`
thread, but the identifier of the currently executing coroutine is appended to it. This identifier 
is consecutively assigned to all created coroutines when debugging mode is turned on.

You can read more about debugging facilities in the documentation for [newCoroutineContext] function.

### Jumping between threads

Run the following code with `-Dkotlinx.coroutines.debug` JVM option:

```kotlin
fun log(msg: String) = println("[${Thread.currentThread().name}] $msg")

fun main(args: Array<String>) {
    val ctx1 = newSingleThreadContext("Ctx1")
    val ctx2 = newSingleThreadContext("Ctx2")
    runBlocking(ctx1) {
        log("Started in ctx1")
        run(ctx2) {
            log("Working in ctx2")
        }
        log("Back to ctx1")
    }
}
```

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/guide/example-context-04.kt)

It demonstrates two new techniques. One is using [runBlocking] with an explicitly specified context, and
the second one is using [run] function to change a context of a coroutine while still staying in the 
same coroutine as you can see in the output below:

```text
[Ctx1 @coroutine#1] Started in ctx1
[Ctx2 @coroutine#1] Working in ctx2
[Ctx1 @coroutine#1] Back to ctx1
```

<!--- TEST -->

### Job in the context

The coroutine [Job] is part of its context. The coroutine can retrieve it from its own context 
using `context[Job]` expression:

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    println("My job is ${context[Job]}")
}
```

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/guide/example-context-05.kt)

It produces somethine like

```
My job is BlockingCoroutine{Active}@65ae6ba4
```

<!--- TEST lines.size == 1 && lines[0].startsWith("My job is BlockingCoroutine{Active}@") -->

So, [isActive][CoroutineScope.isActive] in [CoroutineScope] is just a convenient shortcut for `context[Job]!!.isActive`.

### Children of a coroutine

When [context][CoroutineScope.context] of a coroutine is used to launch another coroutine, 
the [Job] of the new coroutine becomes
a _child_ of the parent coroutine's job. When the parent coroutine is cancelled, all its children
are recursively cancelled, too. 
  
```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    // start a coroutine to process some kind of incoming request
    val request = launch(CommonPool) {
        // it spawns two other jobs, one with its separate context
        val job1 = launch(CommonPool) {
            println("job1: I have my own context and execute independently!")
            delay(1000)
            println("job1: I am not affected by cancellation of the request")
        }
        // and the other inherits the parent context
        val job2 = launch(context) {
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

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/guide/example-context-06.kt)

The output of this code is:

```text
job1: I have my own context and execute independently!
job2: I am a child of the request coroutine
job1: I am not affected by cancellation of the request
main: Who has survived request cancellation?
```

<!--- TEST -->

### Combining contexts

Coroutine context can be combined using `+` operator. The context on the right-hand side replaces relevant entries
of the context on the left-hand side. For example, a [Job] of the parent coroutine can be inherited, while 
its dispatcher replaced:

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    // start a coroutine to process some kind of incoming request
    val request = launch(context) { // use the context of `runBlocking`
        // spawns CPU-intensive child job in CommonPool !!! 
        val job = launch(context + CommonPool) {
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

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/guide/example-context-07.kt)

The expected outcome of this code is: 

```text
job: I am a child of the request coroutine, but with a different dispatcher
main: Who has survived request cancellation?
```

<!--- TEST -->

### Naming coroutines for debugging

Automatically assigned ids are good when coroutines log often and you just need to correlate log records
coming from the same coroutine. However, when coroutine is tied to the processing of a specific request
or doing some specific background task, it is better to name it explicitly for debugging purposes.
[CoroutineName] serves the same function as a thread name. It'll get displayed in the thread name that
is executing this coroutine when debugging more is turned on.

The following example demonstrates this concept:

```kotlin
fun log(msg: String) = println("[${Thread.currentThread().name}] $msg")

fun main(args: Array<String>) = runBlocking(CoroutineName("main")) {
    log("Started main coroutine")
    // run two background value computations
    val v1 = async(CommonPool + CoroutineName("v1coroutine")) {
        log("Computing v1")
        delay(500)
        252
    }
    val v2 = async(CommonPool + CoroutineName("v2coroutine")) {
        log("Computing v2")
        delay(1000)
        6
    }
    log("The answer for v1 / v2 = ${v1.await() / v2.await()}")
}
```

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/guide/example-context-08.kt)

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
the lifecycle of our activity. A job instance is created using [Job()][Job.invoke] factory function
as the following example shows. We need to make sure that all the coroutines are started 
with this job in their context and then a single invocation of [Job.cancel] terminates them all.

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    val job = Job() // create a job object to manage our lifecycle
    // now launch ten coroutines for a demo, each working for a different time
    val coroutines = List(10) { i ->
        // they are all children of our job object
        launch(context + job) { // we use the context of main runBlocking thread, but with our own job object 
            delay(i * 200L) // variable delay 0ms, 200ms, 400ms, ... etc
            println("Coroutine $i is done")
        }
    }
    println("Launched ${coroutines.size} coroutines")
    delay(500L) // delay for half a second
    println("Cancelling job!")
    job.cancel() // cancel our job.. !!!
    delay(1000L) // delay for more to see if our coroutines are still working
}
```

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/guide/example-context-09.kt)

The output of this example is:

```text
Launched 10 coroutines
Coroutine 0 is done
Coroutine 1 is done
Coroutine 2 is done
Cancelling job!
```

<!--- TEST -->

As you can see, only the first three coroutines had printed a message and the others were cancelled 
by a single  invocation of `job.cancel()`. So all we need to do in our hypothetical Android 
application is to create a parent job object when activity is created, use it for child coroutines,
and cancel it when activity is destroyed.

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
    launch(CommonPool) {
        // this might be heavy CPU-consuming computation or async logic, we'll just send five squares
        for (x in 1..5) channel.send(x * x)
    }
    // here we print five received integers:
    repeat(5) { println(channel.receive()) }
    println("Done!")
}
```

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/guide/example-channel-01.kt)

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
    launch(CommonPool) {
        for (x in 1..5) channel.send(x * x)
        channel.close() // we're done sending
    }
    // here we print received values using `for` loop (until the channel is closed)
    for (y in channel) println(y)
    println("Done!")
}
```

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/guide/example-channel-02.kt)

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

There is a convenience coroutine builder named [produce] that makes it easy to do it right:

```kotlin
fun produceSquares() = produce<Int>(CommonPool) {
    for (x in 1..5) send(x * x)
}

fun main(args: Array<String>) = runBlocking<Unit> {
    val squares = produceSquares()
    for (y in squares) println(y)
    println("Done!")
}
```

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/guide/example-channel-03.kt)

<!--- TEST 
1
4
9
16
25
Done!
-->

### Pipelines

Pipeline is a pattern where one coroutine is producing, possibly infinite, stream of values:

```kotlin
fun produceNumbers() = produce<Int>(CommonPool) {
    var x = 1
    while (true) send(x++) // infinite stream of integers starting from 1
}
```

And another coroutine or coroutines are consuming that stream, doing some processing, and producing some other results.
In the below example the numbers are just squared:

```kotlin
fun square(numbers: ReceiveChannel<Int>) = produce<Int>(CommonPool) {
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

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/guide/example-channel-04.kt)

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
[children of a coroutine](#children-of-a-coroutine).

### Prime numbers with pipeline

Let's take pipelines to the extreme with an example that generates prime numbers using a pipeline 
of coroutines. We start with an infinite sequence of numbers. This time we introduce an 
explicit context parameter, so that caller can control where our coroutines run:
 
<!--- INCLUDE kotlinx-coroutines-core/src/test/kotlin/guide/example-channel-05.kt  
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
running the whole pipeline in the context of the main thread:

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    var cur = numbersFrom(context, 2)
    for (i in 1..10) {
        val prime = cur.receive()
        println(prime)
        cur = filter(context, cur, prime)
    }
}
```

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/guide/example-channel-05.kt)

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

Note, that you can build the same pipeline using `buildIterator` coroutine builder from the standard library. 
Replace `produce` with `buildIterator`, `send` with `yield`, `receive` with `next`, 
`ReceiveChannel` with `Iterator`, and get rid of the context. You will not need `runBlocking` either.
However, the benefit of a pipeline that uses channels as shown above is that it can actually use 
multiple CPU cores if you run it in [CommonPool] context.

Anyway, this is an extremely impractical way to find prime numbers. In practice, pipelines do involve some
other suspending invocations (like asynchronous calls to remote services) and these pipelines cannot be
built using `buildSeqeunce`/`buildIterator`, because they do not allow arbitrary suspension, unlike
`produce` which is fully asynchronous.
 
### Fan-out

Multiple coroutines may receive from the same channel, distributing work between themselves.
Let us start with a producer coroutine that is periodically producing integers 
(ten numbers per second):

```kotlin
fun produceNumbers() = produce<Int>(CommonPool) {
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
fun launchProcessor(id: Int, channel: ReceiveChannel<Int>) = launch(CommonPool) {
    while (true) {
        val x = channel.receive()
        println("Processor #$id received $x")
    }
}
```

Now let us launch five processors and let them work for a second. See what happens:

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    val producer = produceNumbers()
    repeat(5) { launchProcessor(it, producer) }
    delay(1000)
    producer.cancel() // cancel producer coroutine and thus kill them all
}
```

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/guide/example-channel-06.kt)

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
(in this example we launch them in the context of the main thread):

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    val channel = Channel<String>()
    launch(context) { sendString(channel, "foo", 200L) }
    launch(context) { sendString(channel, "BAR!", 500L) }
    repeat(6) { // receive first six
        println(channel.receive())
    }
}
```

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/guide/example-channel-07.kt)

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

Both [Channel()][Channel.invoke] factory function and [produce] builder take an optional `capacity` parameter to 
specify _buffer size_. Buffer allows senders to send multiple elements before suspending, 
similar to the `BlockingQueue` with a specified capacity, which blocks when buffer is full.

Take a look at the behavior of the following code:

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    val channel = Channel<Int>(4) // create buffered channel
    launch(context) { // launch sender coroutine
        repeat(10) {
            println("Sending $it") // print before sending each element
            channel.send(it) // will suspend when buffer is full
        }
    }
    // don't receive anything... just wait....
    delay(1000)
}
```

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/guide/example-channel-08.kt)

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

## Shared mutable state and concurrency

Coroutines can be executed concurrently using a multi-threaded dispatcher like [CommonPool]. It presents
all the usual concurrency problems. The main problem being synchronization of access to **shared mutable state**. 
Some solutions to this problem in the land of coroutines are similar to the solutions in the multi-threaded world, 
but others are unique.

### The problem

Let us launch 100k coroutines all doing the same action. We'll also measure their completion time for 
further comparisons:

<!--- INCLUDE .*/example-sync-([0-9]+).kt
import kotlin.system.measureTimeMillis
-->

<!--- INCLUDE .*/example-sync-02.kt
import java.util.concurrent.atomic.AtomicInteger
-->

<!--- INCLUDE .*/example-sync-04.kt
import kotlinx.coroutines.experimental.sync.Mutex
-->

<!--- INCLUDE .*/example-sync-05.kt
import kotlinx.coroutines.experimental.channels.*
-->

```kotlin
suspend fun massiveRun(action: suspend () -> Unit) {
    val n = 100_000
    val time = measureTimeMillis {
        val jobs = List(n) {
            launch(CommonPool) {
                action()
            }
        }
        jobs.forEach { it.join() }
    }
    println("Completed in $time ms")    
}
```

<!--- INCLUDE .*/example-sync-([0-9]+).kt -->

We start with a very simple action that increments a shared mutable variable. 

```kotlin
var counter = 0

fun main(args: Array<String>) = runBlocking<Unit> {
    massiveRun {
        counter++
    }
    println("Counter = $counter")
}
```

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/guide/example-sync-01.kt)

<!--- TEST lines.size == 2 && lines[1].startsWith("Counter = ") -->

What does it print at the end? It is highly unlikely to ever print "100000", because all the 
100k coroutines increment the `counter` concurrently without any synchronization.

### Thread-safe data structures

The general solution that works both for threads and for coroutines is to use a thread-safe (aka synchronized,
linearizable, or atomic) data structure that provides all the necessarily synchronization for the corresponding 
operations that needs to be performed on a shared state. 
In the case of a simple counter we can use `AtomicInteger` class:

```kotlin
var counter = AtomicInteger()

fun main(args: Array<String>) = runBlocking<Unit> {
    massiveRun {
        counter.incrementAndGet()
    }
    println("Counter = ${counter.get()}")
}
```

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/guide/example-sync-02.kt)

<!--- TEST lines.size == 2 && lines[1] == "Counter = 100000" -->

This is the fastest solution for this particular problem. It works for plain counters, collections, queues and other
standard data structures and basic operations on them. However, it does not easily scale to complex
state or to complex operations that do not have ready-to-use thread-safe implementations. 

### Thread confinement

Thread confinement is an approach to the problem of shared mutable state where all access to the particular shared
state is confined to a single thread. It is typically used in UI applications, where all UI state is confined to 
the single event-dispatch/application thread. It is easy to apply with coroutines by using a  
single-threaded context:

```kotlin
val counterContext = newSingleThreadContext("CounterContext")
var counter = 0

fun main(args: Array<String>) = runBlocking<Unit> {
    massiveRun {
        run(counterContext) {
            counter++
        }
    }
    println("Counter = $counter")
}
```

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/guide/example-sync-03.kt)

<!--- TEST lines.size == 2 && lines[1] == "Counter = 100000" -->

### Mutual exclusion

Mutual exclusion solution to the problem is to protect all modifications of the shared state with a _critical section_
that is never executed concurrently. In a blocking world you'd typically use `synchronized` or `ReentrantLock` for that.
Coroutine's alternative is called [Mutex]. It has [lock][Mutex.lock] and [unlock][Mutex.unlock] functions to 
delimit a critical section. The key difference is that `Mutex.lock` is a suspending function. It does not block a thread.

```kotlin
val mutex = Mutex()
var counter = 0

fun main(args: Array<String>) = runBlocking<Unit> {
    massiveRun {
        mutex.lock()
        try { counter++ }
        finally { mutex.unlock() }
    }
    println("Counter = $counter")
}
```

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/guide/example-sync-04.kt)

<!--- TEST lines.size == 2 && lines[1] == "Counter = 100000" -->

### Actors

An actor is a combination of a coroutine, the state that is confined and is encapsulated into this coroutine,
and a channel to communicate with other coroutines. A simple actor can be written as a function, 
but an actor with a complex state is better suited for a class. 

```kotlin
// Message types for counterActor
sealed class CounterMsg
object IncCounter : CounterMsg() // one-way message to increment counter
class GetCounter(val response: SendChannel<Int>) : CounterMsg() // a request with reply

// This function launches a new counter actor
fun counterActor(request: ReceiveChannel<CounterMsg>) = launch(CommonPool) {
    var counter = 0 // actor state
    while (isActive) { // main loop of the actor
        val msg = request.receive()
        when (msg) {
            is IncCounter -> counter++
            is GetCounter -> msg.response.send(counter)
        }
    }
}

fun main(args: Array<String>) = runBlocking<Unit> {
    val request = Channel<CounterMsg>()
    counterActor(request)
    massiveRun {
        request.send(IncCounter)
    }
    val response = Channel<Int>()
    request.send(GetCounter(response))
    println("Counter = ${response.receive()}")
}
```

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/guide/example-sync-05.kt)

<!--- TEST lines.size == 2 && lines[1] == "Counter = 100000" -->

Notice, that it does not matter (for correctness) what context the actor itself is executed in. An actor is
a coroutine and a coroutine is executed sequentially, so confinement of the state to the specific coroutine
works as a solution to the problem of shared mutable state.

## Select expression

Select expression makes it possible to await multiple suspending functions simultaneously and _select_
the first one that becomes available.

<!--- INCLUDE .*/example-select-([0-9]+).kt
import kotlinx.coroutines.experimental.channels.*
import kotlinx.coroutines.experimental.selects.*
-->

### Selecting from channels

Let us have two channels of strings `fizz` and `buzz`. The `fizz` channel produces "Fizz" string every 300 ms:
 
```kotlin
val fizz = produce<String>(CommonPool) { // produce using common thread pool
    while (true) {
        delay(300)
        send("Fizz")
    }
}
```

And the `buzz` channel produces "Buzz!" string every 500 ms:

```kotlin
val buzz = produce<String>(CommonPool) {
    while (true) {
        delay(500)
        send("Buzz!")
    }
}
```

Using [receive][ReceiveChannel.receive] suspending function we can receive _either_ from one channel or the
other. But [select] expression allows us to receive from _both_ simultaneously using its
[onReceive][SelectBuilder.onReceive] clauses:

```kotlin
suspend fun selectFizzBuzz() {
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

Let us run it seven times:

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    repeat(7) {
        selectFizzBuzz()
    }
}
```

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/guide/example-select-01.kt)

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

The [onReceive][SelectBuilder.onReceive] clause in `select` fails when the channel is closed and the corresponding
`select` throws an exception. We can use [onReceiveOrNull][SelectBuilder.onReceiveOrNull] clause to perform a
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
    val a = produce<String>(context) { 
        repeat(4) { send("Hello $it") }
    }
    val b = produce<String>(context) { 
        repeat(4) { send("World $it") }
    }
    repeat(8) { // print first eight results
        println(selectAorB(a, b))
    }
}
```

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/guide/example-select-02.kt)

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

The second observation, is that [onReceiveOrNull][SelectBuilder.onReceiveOrNull] gets immediately selected when the 
channel is already closed.

### Selecting to send

Select expression has [onSend][SelectBuilder.onSend] clause that can be used for a great good in combination 
with a biased nature of selection.

Let us write an example of producer of integers that sends its values to a `side` channel when 
the consumers on its primary channel cannot keep up with it:

```kotlin
fun produceNumbers(side: SendChannel<Int>) = produce<Int>(CommonPool) {
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
    launch(context) { // this is a very fast consumer for the side channel
        for (num in side) println("Side channel has $num")
    }
    for (num in produceNumbers(side)) {
        println("Consuming $num")
        delay(250) // let us digest the consumed number properly, do not hurry
    }
    println("Done consuming")
}
``` 
 
> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/guide/example-select-03.kt)
  
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

Deferred values can be selected using [onAwait][SelectBuilder.onAwait] clause. 
Let us start with an async function that returns a deferred string value after 
a random delay:

<!--- INCLUDE .*/example-select-04.kt
import java.util.*
-->

```kotlin
fun asyncString(time: Int) = async(CommonPool) {
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
    val countActive = list.sumBy { deferred -> if (deferred.isActive) 1 else 0 }
    println("$countActive coroutines are still active")
}
```

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/guide/example-select-04.kt)

The output is:

```text
Deferred 4 produced answer 'Waited for 128 ms'
11 coroutines are still active
```

<!--- TEST -->

### Switch over a channel of deferred values

Let us write a channel producer function that consumes a channel of deferred string values, waits for each received
deferred value, but only until the next deferred value comes over or the channel is closed. This example puts together 
[onReceiveOrNull][SelectBuilder.onReceiveOrNull] and [onAwait][SelectBuilder.onAwait] clauses in the same `select`:

```kotlin
fun switchMapDeferreds(input: ReceiveChannel<Deferred<String>>) = produce<String>(CommonPool) {
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
fun asyncString(str: String, time: Long) = async(CommonPool) {
    delay(time)
    str
}
```

The main function just launches a coroutine to print results of `switchMapDeferreds` and sends some test
data to it:

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    val chan = Channel<Deferred<String>>() // the channel for test
    launch(context) { // launch printing coroutine
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

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/guide/example-select-05.kt)

The result of this code:

```text
BEGIN
Replace
END
Channel was closed
```

<!--- TEST -->

<!--- SITE_ROOT https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core -->
<!--- DOCS_ROOT kotlinx-coroutines-core/target/dokka/kotlinx-coroutines-core -->
<!--- INDEX kotlinx.coroutines.experimental -->
[launch]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/launch.html
[delay]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/delay.html
[runBlocking]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/run-blocking.html
[Job]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-job/index.html
[CancellationException]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-cancellation-exception.html
[yield]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/yield.html
[CoroutineScope.isActive]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/is-active.html
[CoroutineScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-coroutine-scope/index.html
[run]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/run.html
[NonCancellable]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-non-cancellable/index.html
[withTimeout]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/with-timeout.html
[async]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/async.html
[Deferred]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-deferred/index.html
[Deferred.await]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/await.html
[Job.start]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/start.html
[CommonPool]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-common-pool/index.html
[CoroutineDispatcher]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-coroutine-dispatcher/index.html
[CoroutineScope.context]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/context.html
[Unconfined]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-unconfined/index.html
[newCoroutineContext]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/new-coroutine-context.html
[CoroutineName]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-coroutine-name/index.html
[Job.invoke]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/invoke.html
[Job.cancel]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/cancel.html
<!--- INDEX kotlinx.coroutines.experimental.sync -->
[Mutex]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.sync/-mutex/index.html
[Mutex.lock]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.sync/lock.html
[Mutex.unlock]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.sync/unlock.html
<!--- INDEX kotlinx.coroutines.experimental.channels -->
[Channel]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.channels/-channel/index.html
[SendChannel.send]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.channels/send.html
[ReceiveChannel.receive]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.channels/receive.html
[SendChannel.close]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.channels/close.html
[produce]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.channels/produce.html
[Channel.invoke]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.channels/invoke.html
<!--- INDEX kotlinx.coroutines.experimental.selects -->
[select]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.selects/select.html
[SelectBuilder.onReceive]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.selects/on-receive.html
[SelectBuilder.onReceiveOrNull]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.selects/on-receive-or-null.html
[SelectBuilder.onSend]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.selects/on-send.html
[SelectBuilder.onAwait]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.selects/on-await.html
<!--- END -->
