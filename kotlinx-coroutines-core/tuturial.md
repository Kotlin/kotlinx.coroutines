# kotlinx.coroutines core tutorial

This is a DRAFT of a very short tutorial on core features of `kotlinx.coroutines`.

## Your first coroutine

Run the following code:

```kotlin
fun main(args: Array<String>) {
    launch(Here) { // create new coroutine without an explicit threading policy
        delay(1000L) // non-blocking delay for 1 second (default time unit is ms)
        println("World!") // print after delay
    }
    println("Hello,") // main function continues while coroutine is delayed
    Thread.sleep(2000L) // block main thread for 2 seconds to keep JVM alive
}
```

> You can get full code with imports [here](src/test/kotlin/examples/tutorial-example-1.kt)

Run this code:

```
Hello!
World!
```

Essentially, coroutines are light-weight threads. You can achieve the same result replacing
`launch(Here) { ... }` with `thread { ... }` and `delay(...)` with `Thread.sleep(...)`. Try it.

If you start by replacing `launch(Here)` by `thread`, the compiler produces the following error:

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
fun main(args: Array<String>) = runBlocking { // start main coroutine
    launch(Here) { // create new coroutine without an explicit threading policy
        delay(1000L)
        println("World!")
    }
    println("Hello,") // main coroutine continues while child is delayed
    delay(2000L) // non-blocking delay for 2 seconds to keep JVM alive
}
```

> You can get full code with imports [here](src/test/kotlin/examples/tutorial-example-2.kt)

The result is the same, but this code uses only non-blocking `delay`. 

`runBlocking { ... }` works as an adaptor that is used here to start the top-level main coroutine. 
The regular code outside of `runBlocking` _blocks_, until the coroutine inside `runBlocking` works. 

This is also how you write unit-test for suspending functions:
 
```kotlin
class MyTest {
    @Test
    fun testMySuspendingFunction() = runBlocking {
        // here we can use suspending functions using any assertion style that we like
    }
}
```
 
## Waiting for a job

Delaying for a time while a _child_ coroutine is working is not a good approach. Let's explicitly 
wait (in a non-blocking way) until other coroutine that we have launched is complete:

```kotlin
fun main(args: Array<String>) = runBlocking { 
    val job = launch(Here) { // create new coroutine and keep a reference to its Job
        delay(1000L)
        println("World!")
    }
    println("Hello,")
    job.join() // wait until children coroutine completes
}
```

> You can get full code with imports [here](src/test/kotlin/examples/tutorial-example-3.kt)

Now the result is still the same, but the code of the main coroutine is not tied to the duration of
the child coroutine in any way. Much better.

## Extract function refactoring

Let's extract the block of code inside `launch(Here} { ... }` into a separate function. If you 
perform "Extract function" refactoring, you'll get a new function with `suspend` modifier.
That is your first _suspending function_. Suspending functions can be used inside coroutines
just like regular functions, but their additional feature is that they can, in turn, 
use other suspending functions, like `delay` in this example, to _suspend_ execution of a coroutine.

```kotlin
fun main(args: Array<String>) = runBlocking {
    val job = launch(Here) { doWorld() }
    println("Hello,")
    job.join()
}

// this is your first suspending function
suspend fun doWorld() {
    delay(1000L)
    println("World!")
}
```

> You can get full code with imports [here](src/test/kotlin/examples/tutorial-example-4.kt)

## Coroutines ARE light-weight

Run the following code:

```kotlin
fun main(args: Array<String>) = runBlocking {
    val jobs = List(100_000) { // create a lot of coroutines and list their jobs
        launch(Here) {
            delay(1000L)
            print(".")
        }
    }
    jobs.forEach { it.join() } // wait for all jobs to complete
}
```

> You can get full code with imports [here](src/test/kotlin/examples/tutorial-example-5.kt)

It starts 100K coroutines and, after a second, each coroutine prints a dot. 
Now, try that with threads. What would happen? (Most likely your code will produce some sort of out-of-memory error)
