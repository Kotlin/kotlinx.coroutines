# Guide to kotlinx.coroutines by example

This is a short guide on core features of `kotlinx.coroutines` with a series of examples.

## Your first coroutine

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

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/examples/example-01.kt)

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

## Bridging blocking and non-blocking worlds

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

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/examples/example-02.kt)

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
 
## Waiting for a job

Delaying for a time while a _child_ coroutine is working is not a good approach. Let's explicitly 
wait (in a non-blocking way) until the other coroutine that we have launched is complete:

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

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/examples/example-03.kt)

Now the result is still the same, but the code of the main coroutine is not tied to the duration of
the child coroutine in any way. Much better.

## Extract function refactoring

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

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/examples/example-04.kt)

## Coroutines ARE light-weight

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

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/examples/example-05.kt)

It starts 100K coroutines and, after a second, each coroutine prints a dot. 
Now, try that with threads. What would happen? (Most likely your code will produce some sort of out-of-memory error)

## Coroutines are like daemon threads

The following code launches a long-running coroutine that prints "I'm sleeping" twice a second and then 
returns from the main thread after some delay:

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

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/examples/example-06.kt)

You can run and see that it prints three lines and terminates:

```
I'm sleeping 0 ...
I'm sleeping 1 ...
I'm sleeping 2 ...
```

Active coroutines do not keep the process alive. They are like daemon threads.

## Cancelling coroutine execution

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
    println("I'm tired of waiting!")
    job.cancel() // cancels the job
    delay(1300L) // delay a bit to ensure it was cancelled indeed
    println("Now I can quit.")
}
``` 

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/examples/example-07.kt)

## Cancellation is cooperative

Coroutine cancellation is _cooperative_. A coroutine code has to cooperate be cancellable.
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
    println("I'm tired of waiting!")
    job.cancel() // cancels the job
    delay(1300L) // delay a bit to see if it was cancelled....
    println("Now I can quit.")
}
```

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/examples/example-08.kt)

Run it to see that it continues to print "I'm sleeping" even after cancellation.

## Making computation code cancellable

There are two approaches to making computation code cancellable. The first one is to periodically 
invoke any suspending function. There is a `yield` function that is a good choice for that purpose.
The other one is to explicitly check the cancellation status. The following example demonstrates
the later approach. 

Replace `while (true)` in the previous example with `while (isActive)` and rerun it. 

> You can get full code [here](kotlinx-coroutines-core/src/test/kotlin/examples/example-09.kt)

As you can see, now this loop can be cancelled. `isActive` is a property that is available inside
the code of coroutines via `CoroutineScope` object.


