<!--- TEST_NAME BasicsGuideTest -->

**Table of contents**

<!--- TOC -->

* [Coroutine Basics](#coroutine-basics)
  * [Your first coroutine](#your-first-coroutine)
  * [Bridging blocking and non-blocking worlds](#bridging-blocking-and-non-blocking-worlds)
  * [Waiting for a job](#waiting-for-a-job)
  * [Structured concurrency](#structured-concurrency)
  * [Scope builder](#scope-builder)
  * [Extract function refactoring](#extract-function-refactoring)
  * [Coroutines ARE light-weight](#coroutines-are-light-weight)
  * [Global coroutines are like daemon threads](#global-coroutines-are-like-daemon-threads)

<!--- END -->

## Coroutine Basics

This section covers basic coroutine concepts.

### Your first coroutine

Run the following code:

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

```kotlin
import kotlinx.coroutines.*

fun main() {
    GlobalScope.launch { // launch a new coroutine in background and continue
        delay(1000L) // non-blocking delay for 1 second (default time unit is ms)
        println("World!") // print after delay
    }
    println("Hello,") // main thread continues while coroutine is delayed
    Thread.sleep(2000L) // block main thread for 2 seconds to keep JVM alive
}
```

</div>

> You can get the full code [here](../kotlinx-coroutines-core/jvm/test/guide/example-basic-01.kt).

You will see the following result:

```text
Hello,
World!
```

<!--- TEST -->

Essentially, coroutines are light-weight threads.
They are launched with [launch] _coroutine builder_ in a context of some [CoroutineScope].
Here we are launching a new coroutine in the [GlobalScope], meaning that the lifetime of the new
coroutine is limited only by the lifetime of the whole application.  

You can achieve the same result by replacing
`GlobalScope.launch { ... }` with `thread { ... }`, and `delay(...)` with `Thread.sleep(...)`. 
Try it (don't forget to import `kotlin.concurrent.thread`).

If you start by replacing `GlobalScope.launch` with `thread`, the compiler produces the following error:

```
Error: Kotlin: Suspend functions are only allowed to be called from a coroutine or another suspend function
```

That is because [delay] is a special _suspending function_ that does not block a thread, but _suspends_ the
coroutine, and it can be only used from a coroutine.

### Bridging blocking and non-blocking worlds

The first example mixes _non-blocking_ `delay(...)` and _blocking_ `Thread.sleep(...)` in the same code. 
It is easy to lose track of which one is blocking and which one is not. 
Let's be explicit about blocking using the [runBlocking] coroutine builder:

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

```kotlin
import kotlinx.coroutines.*

fun main() { 
    GlobalScope.launch { // launch a new coroutine in background and continue
        delay(1000L)
        println("World!")
    }
    println("Hello,") // main thread continues here immediately
    runBlocking {     // but this expression blocks the main thread
        delay(2000L)  // ... while we delay for 2 seconds to keep JVM alive
    } 
}
```

</div>

> You can get the full code [here](../kotlinx-coroutines-core/jvm/test/guide/example-basic-02.kt).

<!--- TEST
Hello,
World!
-->

The result is the same, but this code uses only non-blocking [delay]. 
The main thread invoking `runBlocking` _blocks_ until the coroutine inside `runBlocking` completes. 

This example can be also rewritten in a more idiomatic way, using `runBlocking` to wrap 
the execution of the main function:

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

```kotlin
import kotlinx.coroutines.*

fun main() = runBlocking<Unit> { // start main coroutine
    GlobalScope.launch { // launch a new coroutine in background and continue
        delay(1000L)
        println("World!")
    }
    println("Hello,") // main coroutine continues here immediately
    delay(2000L)      // delaying for 2 seconds to keep JVM alive
}
```

</div>

> You can get the full code [here](../kotlinx-coroutines-core/jvm/test/guide/example-basic-03.kt).

<!--- TEST
Hello,
World!
-->

Here `runBlocking<Unit> { ... }` works as an adaptor that is used to start the top-level main coroutine. 
We explicitly specify its `Unit` return type, because a well-formed `main` function in Kotlin has to return `Unit`.

This is also a way to write unit tests for suspending functions:

<!--- INCLUDE
import kotlinx.coroutines.*
-->

<div class="sample" markdown="1" theme="idea" data-highlight-only>
 
```kotlin
class MyTest {
    @Test
    fun testMySuspendingFunction() = runBlocking<Unit> {
        // here we can use suspending functions using any assertion style that we like
    }
}
```

</div>

<!--- CLEAR -->
 
### Waiting for a job

Delaying for a time while another coroutine is working is not a good approach. Let's explicitly 
wait (in a non-blocking way) until the background [Job] that we have launched is complete:

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

```kotlin
import kotlinx.coroutines.*

fun main() = runBlocking {
//sampleStart
    val job = GlobalScope.launch { // launch a new coroutine and keep a reference to its Job
        delay(1000L)
        println("World!")
    }
    println("Hello,")
    job.join() // wait until child coroutine completes
//sampleEnd    
}
```

</div>

> You can get the full code [here](../kotlinx-coroutines-core/jvm/test/guide/example-basic-04.kt).

<!--- TEST
Hello,
World!
-->

Now the result is still the same, but the code of the main coroutine is not tied to the duration of
the background job in any way. Much better.

### Structured concurrency

There is still something to be desired for practical usage of coroutines. 
When we use `GlobalScope.launch`, we create a top-level coroutine. Even though it is light-weight, it still 
consumes some memory resources while it runs. If we forget to keep a reference to the newly launched 
coroutine, it still runs. What if the code in the coroutine hangs (for example, we erroneously
delay for too long), what if we launched too many coroutines and ran out of memory? 
Having to manually keep references to all the launched coroutines and [join][Job.join] them is error-prone. 

There is a better solution. We can use structured concurrency in our code. 
Instead of launching coroutines in the [GlobalScope], just like we usually do with threads (threads are always global), 
we can launch coroutines in the specific scope of the operation we are performing. 

In our example, we have a `main` function that is turned into a coroutine using the [runBlocking] coroutine builder.
Every coroutine builder, including `runBlocking`, adds an instance of [CoroutineScope] to the scope of its code block. 
We can launch coroutines in this scope without having to `join` them explicitly, because
an outer coroutine (`runBlocking` in our example) does not complete until all the coroutines launched
in its scope complete. Thus, we can make our example simpler:

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

```kotlin
import kotlinx.coroutines.*

fun main() = runBlocking { // this: CoroutineScope
    launch { // launch a new coroutine in the scope of runBlocking
        delay(1000L)
        println("World!")
    }
    println("Hello,")
}
```

</div>

> You can get the full code [here](../kotlinx-coroutines-core/jvm/test/guide/example-basic-05.kt).

<!--- TEST
Hello,
World!
-->

### Scope builder

In addition to the coroutine scope provided by different builders, it is possible to declare your own scope using the
[coroutineScope] builder. It creates a coroutine scope and does not complete until all launched children complete. 

[runBlocking] and [coroutineScope] may look similar because they both wait for their body and all its children to complete.
The main difference is that the [runBlocking] method _blocks_ the current thread for waiting,
while [coroutineScope] just suspends, releasing the underlying thread for other usages.
Because of that difference, [runBlocking] is a regular function and [coroutineScope] is a suspending function.

It can be demonstrated by the following example:

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

```kotlin
import kotlinx.coroutines.*

fun main() = runBlocking { // this: CoroutineScope
    launch { 
        delay(200L)
        println("Task from runBlocking")
    }
    
    coroutineScope { // Creates a coroutine scope
        launch {
            delay(500L) 
            println("Task from nested launch")
        }
    
        delay(100L)
        println("Task from coroutine scope") // This line will be printed before the nested launch
    }
    
    println("Coroutine scope is over") // This line is not printed until the nested launch completes
}
```

</div>

> You can get the full code [here](../kotlinx-coroutines-core/jvm/test/guide/example-basic-06.kt).

<!--- TEST
Task from coroutine scope
Task from runBlocking
Task from nested launch
Coroutine scope is over
-->

Note that right after the "Task from coroutine scope" message (while waiting for nested launch)
 "Task from runBlocking" is executed and printed — even though the [coroutineScope] is not completed yet. 

### Extract function refactoring

Let's extract the block of code inside `launch { ... }` into a separate function. When you 
perform "Extract function" refactoring on this code, you get a new function with the `suspend` modifier.
This is your first _suspending function_. Suspending functions can be used inside coroutines
just like regular functions, but their additional feature is that they can, in turn, 
use other suspending functions (like `delay` in this example) to _suspend_ execution of a coroutine.

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

```kotlin
import kotlinx.coroutines.*

fun main() = runBlocking {
    launch { doWorld() }
    println("Hello,")
}

// this is your first suspending function
suspend fun doWorld() {
    delay(1000L)
    println("World!")
}
```

</div>

> You can get the full code [here](../kotlinx-coroutines-core/jvm/test/guide/example-basic-07.kt).

<!--- TEST
Hello,
World!
-->


But what if the extracted function contains a coroutine builder which is invoked on the current scope?
In this case, the `suspend` modifier on the extracted function is not enough. Making `doWorld` an extension
method on `CoroutineScope` is one of the solutions, but it may not always be applicable as it does not make the API clearer.
The idiomatic solution is to have either an explicit `CoroutineScope` as a field in a class containing the target function
or an implicit one when the outer class implements `CoroutineScope`.
As a last resort, [CoroutineScope(coroutineContext)][CoroutineScope()] can be used, but such an approach is structurally unsafe 
because you no longer have control on the scope of execution of this method. Only private APIs can use this builder.

### Coroutines ARE light-weight

Run the following code:

<div class="sample" markdown="1" theme="idea" data-highlight-only>

```kotlin
import kotlinx.coroutines.*

fun main() = runBlocking {
    repeat(100_000) { // launch a lot of coroutines
        launch {
            delay(1000L)
            print(".")
        }
    }
}
```

</div>

> You can get the full code [here](../kotlinx-coroutines-core/jvm/test/guide/example-basic-08.kt).

<!--- TEST lines.size == 1 && lines[0] == ".".repeat(100_000) -->

It launches 100K coroutines and, after a second, each coroutine prints a dot. 

Now, try that with threads. What would happen? (Most likely your code will produce some sort of out-of-memory error)

### Global coroutines are like daemon threads

The following code launches a long-running coroutine in [GlobalScope] that prints "I'm sleeping" twice a second and then 
returns from the main function after some delay:

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

```kotlin
import kotlinx.coroutines.*

fun main() = runBlocking {
//sampleStart
    GlobalScope.launch {
        repeat(1000) { i ->
            println("I'm sleeping $i ...")
            delay(500L)
        }
    }
    delay(1300L) // just quit after delay
//sampleEnd    
}
```

</div>

> You can get the full code [here](../kotlinx-coroutines-core/jvm/test/guide/example-basic-09.kt).

You can run and see that it prints three lines and terminates:

```text
I'm sleeping 0 ...
I'm sleeping 1 ...
I'm sleeping 2 ...
```

<!--- TEST -->

Active coroutines that were launched in [GlobalScope] do not keep the process alive. They are like daemon threads.

<!--- MODULE kotlinx-coroutines-core -->
<!--- INDEX kotlinx.coroutines -->
[launch]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/launch.html
[CoroutineScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-coroutine-scope/index.html
[GlobalScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-global-scope/index.html
[delay]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/delay.html
[runBlocking]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/run-blocking.html
[Job]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-job/index.html
[Job.join]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-job/join.html
[coroutineScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/coroutine-scope.html
[CoroutineScope()]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-coroutine-scope.html
<!--- END -->


