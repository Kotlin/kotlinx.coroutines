<!---

Copyright 2016-2017 JetBrains s.r.o.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

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
  * [Concurrent using deferred value](#concurrent-using-deferred-value)
  * [Lazily deferred value](#lazily-deferred-value)
* [Coroutine context and dispatchers](#coroutine-context-and-dispatchers)
  * [Dispatchers and threads](#dispatchers-and-threads)
  * [Unconfined vs confined dispatcher](#unconfined-vs-confined-dispatcher)
  * [Debugging coroutines and threads](#debugging-coroutines-and-threads)
  * [Jumping between threads](#jumping-between-threads)
  * [Job in the context](#job-in-the-context)
  * [Children of a coroutine](#children-of-a-coroutine)
  * [Combining contexts](#combining-contexts)
  * [Naming coroutines for debugging](#naming-coroutines-for-debugging)
* [Channels](#channels)
  * [Channel basics](#channel-basics)
  * [Closing and iteration over channels](#closing-and-iteration-over-channels)
  * [Building channel producers](#building-channel-producers)
  * [Pipelines](#pipelines)
  * [Prime numbers with pipeline](#prime-numbers-with-pipeline)
  * [Fan-out](#fan-out)
  * [Fan-in](#fan-in)
  * [Buffered channels](#buffered-channels)

<!--- KNIT kotlinx-coroutines-core/src/test/kotlin/guide/.*\.kt -->

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

```
Hello,
World!
```

Essentially, coroutines are light-weight threads. You can achieve the same result replacing
`launch(CommonPool) { ... }` with `thread { ... }` and `delay(...)` with `Thread.sleep(...)`. Try it.

If you start by replacing `launch(CommonPool)` by `thread`, the compiler produces the following error:

```
Error: Kotlin: Suspend functions are only allowed to be called from a coroutine or another suspend function
```

That is because `delay` is a special _suspending function_ that does not block a thread, but _suspends_
coroutine and it can be only used from a coroutine.

### Bridging blocking and non-blocking worlds

The first example mixes _non-blocking_ `delay(...)` and _blocking_ `Thread.sleep(...)` in the same
code of `main` function. It is easy to get lost. Let's cleanly separate blocking and non-blocking
worlds by using `runBlocking { ... }`:

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

The result is the same, but this code uses only non-blocking `delay`. 

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
wait (in a non-blocking way) until the background job coroutine that we have launched is complete:

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

```
I'm sleeping 0 ...
I'm sleeping 1 ...
I'm sleeping 2 ...
```

Active coroutines do not keep the process alive. They are like daemon threads.

## Cancellation and timeouts

This section covers coroutine cancellation and timeouts.

### Cancelling coroutine execution

In small application the return from "main" method might sound like a good idea to get all coroutines 
implicitly terminated. In a larger, long-running application, you need finer-grained control.
The `launch` function returns a `Job` that can be used to cancel running coroutine:
 
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

```
I'm sleeping 0 ...
I'm sleeping 1 ...
I'm sleeping 2 ...
main: I'm tired of waiting!
main: Now I can quit.
```

As soon as main invokes `job.cancel`, we don't see any output from the other coroutine because it was cancelled. 

### Cancellation is cooperative

Coroutine cancellation is _cooperative_. A coroutine code has to cooperate to be cancellable.
All the suspending functions in `kotlinx.coroutines` are _cancellable_. They check for cancellation of 
coroutine and throw `CancellationException` when cancelled. However, if a coroutine is working in 
a computation and does not check for cancellation, then it cannot be cancelled, like the following 
example shows:

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    val job = launch(CommonPool) {
        var nextPrintTime = 0L
        var i = 0
        while (true) { // computation loop
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

### Making computation code cancellable

There are two approaches to making computation code cancellable. The first one is to periodically 
invoke a suspending function. There is a `yield` function that is a good choice for that purpose.
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

As you can see, now this loop can be cancelled. `isActive` is a property that is available inside
the code of coroutines via `CoroutineScope` object.

### Closing resources with finally

Cancellable suspending functions throw `CancellationException` on cancellation which can be handled in 
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

```
I'm sleeping 0 ...
I'm sleeping 1 ...
I'm sleeping 2 ...
main: I'm tired of waiting!
I'm running finally
main: Now I can quit.
```

### Run non-cancellable block

Any attempt to use a suspending function in the `finally` block of the previous example will cause
`CancellationException`, because the coroutine running this code is cancelled. Usually, this is not a 
problem, since all well-behaving closing operations (closing a file, cancelling a job, or closing any kind of a 
communication channel) are usually non-blocking and do not involve any suspending functions. However, in the 
rare case when you need to suspend in the cancelled coroutine you can wrap the corresponding code in
`run(NonCancellable) {...}` as the following example shows:
 
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

### Timeout

The most obvious reason to cancel coroutine execution in practice, 
is because its execution time has exceeded some timeout.
While you can manually track the reference to the corresponding `job` and launch a separate coroutine to cancel 
the tracked one after delay, there is a ready to use `withTimeout(...) {...}` function that does it.
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

```
I'm sleeping 0 ...
I'm sleeping 1 ...
I'm sleeping 2 ...
Exception in thread "main" java.util.concurrent.CancellationException: Timed out waiting for 1300 MILLISECONDS
```

We have not seen the `CancellationException` stack trace printed on the console before. That is because
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
code, is _sequential_ by default. The following example demonstrates that by measuring the total 
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

```
The answer is 42
Completed in 2017 ms
```

### Concurrent using deferred value

What if there are no dependencies between invocation of `doSomethingUsefulOne` and `doSomethingUsefulTwo` and
we want to get the answer faster, by doing both _concurrently_? This is where `defer` comes to helps. 
 
Conceptually, `defer` is just like `launch`. It starts a separate coroutine which is a light-weight thread 
that works concurrently with all the other coroutines. The difference is that `launch` returns a `Job` and 
does not carry any resulting value, while `defer` returns a `Deferred` -- a kind of light-weight non-blocking future
that represent a promise to provide result later. You can use `.await()` on a deferred value to get its eventual result,
but `Deferred` is also a `Job`, so you can cancel it if needed.
 
```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    val time = measureTimeMillis {
        val one = defer(CommonPool) { doSomethingUsefulOne() }
        val two = defer(CommonPool) { doSomethingUsefulTwo() }
        println("The answer is ${one.await() + two.await()}")
    }
    println("Completed in $time ms")
}
```

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/guide/example-compose-02.kt)

It produces something like this:

```
The answer is 42
Completed in 1017 ms
```

This is twice as fast, because we have concurrent execution of two coroutines. 
Note, that concurrency with coroutines is always explicit.

### Lazily deferred value

There is a lazy alternative to `defer` that is called `lazyDefer`. It is just like `defer`, but it 
starts coroutine only when its result is needed by some `await` or if a special `start` function 
is invoked. Run the following example:

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    val time = measureTimeMillis {
        val one = lazyDefer(CommonPool) { doSomethingUsefulOne() }
        val two = lazyDefer(CommonPool) { doSomethingUsefulTwo() }
        println("The answer is ${one.await() + two.await()}")
    }
    println("Completed in $time ms")
}
```

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/guide/example-compose-03.kt)

It produces something like this:

```
The answer is 42
Completed in 2017 ms
```

So, we are back to two sequential execution, because we _first_ await for the `one` deferred, _and then_ await
for the second one. It is not the intended use-case for `lazyDefer`. It is designed as a replacement for
the standard `lazy` function in cases when computation of the value involve suspending functions.

## Coroutine context and dispatchers

We've already seen `launch(CommonPool) {...}`, `defer(CommonPool) {...}`, `run(NonCancellable) {...}`, etc.
In these code snippets `CommonPool` and `NonCancellable` are _coroutine contexts_. 
This section covers other available choices.

### Dispatchers and threads

Coroutine context includes a _coroutine dispatcher_ which determines what thread or threads 
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

```
 'Unconfined': I'm working in thread main
 'CommonPool': I'm working in thread ForkJoinPool.commonPool-worker-1
     'newSTC': I'm working in thread MyOwnThread
    'context': I'm working in thread main
```

The difference between parent `context` and `Unconfied` context will be shown later.

### Unconfined vs confined dispatcher
 
The `Unconfined` coroutine dispatcher starts coroutine in the caller thread, but only until the
first suspension point. After suspension it resumes in the thread that is fully determined by the
suspending function that was invoked. Unconfined dispatcher is appropriate when coroutine does not
consume CPU time nor updates any shared data (like UI) that is confined to a specific thread. 

On the other side, `context` property that is available inside the block of any coroutine 
via `CoroutineScope` interface, is a reference to a context of this particular coroutine. 
This way, a parent context can be inherited. The default context of `runBlocking`, in particular,
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
 
```
 'Unconfined': I'm working in thread main
    'context': I'm working in thread main
 'Unconfined': After delay in thread kotlinx.coroutines.ScheduledExecutor
    'context': After delay in thread main
```
 
So, the coroutine the had inherited `context` of `runBlocking {...}` continues to execute in the `main` thread,
while the unconfined one had resumed in the scheduler thread that `delay` function is using.

### Debugging coroutines and threads

Coroutines can suspend on one thread and resume on another thread with `Unconfined` dispatcher or 
with a multi-threaded dispatcher like `CommonPool`. Even with a single-threaded dispatcher it might be hard to
figure out what coroutine was doing what, where, and when. The common approach to debugging applications with 
threads is to print the thread name in the log file on each log statement. This feature is universally supported
by logging frameworks. When using coroutines, the thread name alone does not give much of a context, so 
`kotlinx.coroutines` includes debugging facilities to make it easier. 

Run the following code with `-Dkotlinx.coroutines.debug` JVM option:

```kotlin
fun log(msg: String) = println("[${Thread.currentThread().name}] $msg")

fun main(args: Array<String>) = runBlocking<Unit> {
    val a = defer(context) {
        log("I'm computing a piece of the answer")
        6
    }
    val b = defer(context) {
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

```
[main @coroutine#2] I'm computing a piece of the answer
[main @coroutine#3] I'm computing another piece of the answer
[main @coroutine#1] The answer is 42
```

The `log` function prints the name of the thread in square brackets and you can see, that it is the `main`
thread, but the identifier of the currently executing coroutine is appended to it. This identifier 
is consecutively assigned to all created coroutines when debugging mode is turned on.

You can read more about debugging facilities in the documentation for `newCoroutineContext` function.

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

It demonstrates two new techniques. One is using `runBlocking` with an explicitly specified context, and
the second one is using `run(context) {...}` to change a context of a coroutine while still staying in the 
same coroutine as you can see in the output below:

```
[Ctx1 @coroutine#1] Started in ctx1
[Ctx2 @coroutine#1] Working in ctx2
[Ctx1 @coroutine#1] Back to ctx1
```

### Job in the context

The coroutine `Job` is part of its context. The coroutine can retrieve it from its own context 
using `context[Job]` expression:

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    println("My job is ${context[Job]}")
}
```

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/guide/example-context-05.kt)

It produces

```
My job is BlockingCoroutine{isActive=true}
```

So, `isActive` in `CoroutineScope` is just a convenient shortcut for `context[Job]!!.isActive`.

### Children of a coroutine

When `context` of a coroutine is used to launch another coroutine, the `Job` of the new coroutine becomes
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

```
job1: I have my own context and execute independently!
job2: I am a child of the request coroutine
job1: I am not affected by cancellation of the request
main: Who has survived request cancellation?
```

### Combining contexts

Coroutine context can be combined using `+` operator. The context on the right-hand side replaces relevant entries
of the context on the left-hand side. For example, a `Job` of the parent coroutine can be inherited, while 
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

```
job: I am a child of the request coroutine, but with a different dispatcher
main: Who has survived request cancellation?
```

### Naming coroutines for debugging

Automatically assigned ids are good when coroutines log often and you just need to correlate log records
coming from the same coroutine. However, when coroutine is tied to the processing of a specific request
or doing some specific background task, it is better to name it explicitly for debugging purposes.
Coroutine name serves the same function as a thread name. It'll get displayed in the thread name that
is executing this coroutine when debugging more is turned on.

The following example demonstrates this concept:

```kotlin
fun log(msg: String) = println("[${Thread.currentThread().name}] $msg")

fun main(args: Array<String>) = runBlocking(CoroutineName("main")) {
    log("Started main coroutine")
    // run two background value computations
    val v1 = defer(CommonPool + CoroutineName("v1coroutine")) {
        log("Computing v1")
        delay(500)
        252
    }
    val v2 = defer(CommonPool + CoroutineName("v2coroutine")) {
        log("Computing v2")
        delay(1000)
        6
    }
    log("The answer for v1 / v2 = ${v1.await() / v2.await()}")
}
```

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/guide/example-context-08.kt)

The output it produces with `-Dkotlinx.coroutines.debug` JVM option is similar to:
 
```
[main @main#1] Started main coroutine
[ForkJoinPool.commonPool-worker-1 @v1coroutine#2] Computing v1
[ForkJoinPool.commonPool-worker-2 @v2coroutine#3] Computing v2
[main @main#1] The answer for v1 / v2 = 42
```

## Channels

Deferred values provide a convenient way to transfer a single value between coroutines.
Channels provide a way to transfer a stream of values.

<!--- INCLUDE .*/example-channel-([0-9]+).kt
import kotlinx.coroutines.experimental.channels.*
-->

### Channel basics

A `Channel` is conceptually very similar to `BlockingQueue`. One key difference is that
instead of a blocking `put` operation it has a suspending `send`, and instead of 
a blocking `take` operation it has a suspending `receive`.

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

### Closing and iteration over channels 

Unlike a queue, a channel can be closed to indicate that no more elements are coming. 
On the receiver side it is convenient to use a regular `for` loop to receive elements 
from the channel. 
 
Conceptually, a `close` is like sending a special close token to the channel. 
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

### Building channel producers

The pattern where a coroutine is producing a sequence of elements into a channel is quite common.
You could abstract such a producer into a function that takes channel as its parameter, but this goes contrary
to common sense that results must be returned from functions. Here is a convenience 
coroutine builder named `buildChannel` that makes it easy to do it right:

```kotlin
fun produceSquares() = buildChannel<Int>(CommonPool) {
    for (x in 1..5) send(x * x)
}

fun main(args: Array<String>) = runBlocking<Unit> {
    val squares = produceSquares()
    for (y in squares) println(y)
    println("Done!")
}
```

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/guide/example-channel-03.kt)

### Pipelines

Pipeline is a pattern where one coroutine is producing, possibly infinite, stream of values:

```kotlin
fun produceNumbers() = buildChannel<Int>(CommonPool) {
    var x = 1
    while (true) send(x++) // infinite stream of integers starting from 1
}
```

And another coroutine or coroutines are receiving that stream, doing some processing, and sending the result.
In the below example the numbers are just squared:

```kotlin
fun square(numbers: ReceiveChannel<Int>) = buildChannel<Int>(CommonPool) {
    for (x in numbers) send(x * x)
}
```

The main code starts and connects pipeline:

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
fun numbersFrom(context: CoroutineContext, start: Int) = buildChannel<Int>(context) {
    var x = start
    while (true) send(x++) // infinite stream of integers from start
}
```

The following pipeline stage filters an incoming stream of numbers, removing all the numbers 
that are divisible by the given prime number:

```kotlin
fun filter(context: CoroutineContext, numbers: ReceiveChannel<Int>, prime: Int) = buildChannel<Int>(context) {
    for (x in numbers) if (x % prime != 0) send(x)
}
```

Now we build our pipeline by starting a stream of numbers from 2, taking a prime number from the current channel, 
and launching new pipeline stage for each prime number found. The following example prints the first ten prime numbers, 
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

```
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

### Fan-out

Multiple coroutines may receive from the same channel, distributing work between themselves.
Let us start with a producer coroutine that is periodically producing integers 
(ten numbers per second):

```kotlin
fun produceNumbers() = buildChannel<Int>(CommonPool) {
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

```
foo
foo
BAR!
foo
foo
BAR!
```

### Buffered channels

The channels shown so far had no buffer. Unbuffered channels transfer elements when sender and receiver 
meet each other (aka rendezvous). If send is invoked first, then it is suspended until receive is invoked, 
if receive is invoked first, it is suspended until send is invoked.
 
Both `Channel()` factory and `buildChanner{}` builder take an optional `capacity` parameter to 
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

```
Sending 0
Sending 1
Sending 2
Sending 3
Sending 4
```

The first four elements are added to the buffer and the sender suspends when trying to send the fifth one.
