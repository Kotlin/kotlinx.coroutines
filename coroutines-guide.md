# Guide to kotlinx.coroutines by example

This is a short guide on core features of `kotlinx.coroutines` with a series of examples.

## Table of contents

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

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/examples/example-11.kt)

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

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/examples/example-12.kt)

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

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/examples/example-13.kt)

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

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/examples/example-14.kt)

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

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/examples/example-15.kt)

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

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/examples/example-16.kt)

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

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/examples/example-21.kt)

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

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/examples/example-22.kt)

Run it to see that it continues to print "I'm sleeping" even after cancellation.

### Making computation code cancellable

There are two approaches to making computation code cancellable. The first one is to periodically 
invoke a suspending function. There is a `yield` function that is a good choice for that purpose.
The other one is to explicitly check the cancellation status. Let us try the later approach. 

Replace `while (true)` in the previous example with `while (isActive)` and rerun it. 

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/examples/example-23.kt)

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

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/examples/example-24.kt)

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

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/examples/example-25.kt)

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

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/examples/example-26.kt)

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
remote service call or computation. We'll just pretend they are useful, but each one will just actaully
delay for a second for the purpose of this example:

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

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/examples/example-31.kt)

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

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/examples/example-32.kt)

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

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/examples/example-33.kt)

It produces something like this:

```
The answer is 42
Completed in 2017 ms
```

So, we are back to two sequential execution, because we _first_ await for the `one` deferred, _and then_ await
for the second one. It is not the intended use-case for `lazyDefer`. It is designed as a replacement for
the standard `lazy` function in cases when computation of the value involve suspending functions.



