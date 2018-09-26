<!--- INCLUDE .*/example-([a-z]+)-([0-9a-z]+)\.kt 
/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

// This file was automatically generated from coroutines-guide.md by Knit tool. Do not edit.
package kotlinx.coroutines.experimental.guide.$$1$$2

import kotlinx.coroutines.experimental.*
-->
<!--- KNIT     ../core/kotlinx-coroutines-core/test/guide/.*\.kt -->
<!--- TEST_OUT ../core/kotlinx-coroutines-core/test/guide/test/BasicsGuideTest.kt
// This file was automatically generated from coroutines-guide.md by Knit tool. Do not edit.
package kotlinx.coroutines.experimental.guide.test

import org.junit.Test

class BasicsGuideTest {
--> 

## Table of contents

<!--- TOC -->

* [Coroutine basics](#coroutine-basics)
  * [Your first coroutine](#your-first-coroutine)
  * [Bridging blocking and non-blocking worlds](#bridging-blocking-and-non-blocking-worlds)
  * [Waiting for a job](#waiting-for-a-job)
  * [Structured concurrency](#structured-concurrency)
  * [Scope builder](#scope-builder)
  * [Extract function refactoring](#extract-function-refactoring)
  * [Coroutines ARE light-weight](#coroutines-are-light-weight)
  * [Global coroutines are like daemon threads](#global-coroutines-are-like-daemon-threads)

<!--- END_TOC -->


## Coroutine basics

This section covers basic coroutine concepts.

### Your first coroutine

Run the following code:

<div class="sample" markdown="1" theme="idea">

```kotlin
fun main(args: Array<String>) {
    GlobalScope.launch { // launch new coroutine in background and continue
        delay(1000L) // non-blocking delay for 1 second (default time unit is ms)
        println("World!") // print after delay
    }
    println("Hello,") // main thread continues while coroutine is delayed
    Thread.sleep(2000L) // block main thread for 2 seconds to keep JVM alive
}
```

</div>

> You can get full code [here](../core/kotlinx-coroutines-core/test/guide/example-basic-01.kt)

Run this code:

```text
Hello,
World!
```

<!--- TEST -->

Essentially, coroutines are light-weight threads.
They are launched with [launch] _coroutine builder_ in a context of some [CoroutineScope].
Here we are launching a new coroutine in the [GlobalScope], meaning that the lifetime of the new
coroutine is limited only by the lifetime of the whole application.  

You can achieve the same result replacing
`GlobalScope.launch { ... }` with `thread { ... }` and `delay(...)` with `Thread.sleep(...)`. Try it.

If you start by replacing `GlobalScope.launch` by `thread`, the compiler produces the following error:

```
Error: Kotlin: Suspend functions are only allowed to be called from a coroutine or another suspend function
```

That is because [delay] is a special _suspending function_ that does not block a thread, but _suspends_
coroutine and it can be only used from a coroutine.

### Bridging blocking and non-blocking worlds

The first example mixes _non-blocking_ `delay(...)` and _blocking_ `Thread.sleep(...)` in the same code. 
It is easy to get lost which one is blocking and which one is not. 
Let's be explicit about blocking using [runBlocking] coroutine builder:

<div class="sample" markdown="1" theme="idea">

```kotlin
fun main(args: Array<String>) { 
    GlobalScope.launch { // launch new coroutine in background and continue
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

> You can get full code [here](../core/kotlinx-coroutines-core/test/guide/example-basic-02.kt)

<!--- TEST
Hello,
World!
-->

The result is the same, but this code uses only non-blocking [delay]. 
The main thread, that invokes `runBlocking`, _blocks_ until the coroutine inside `runBlocking` completes. 

This example can be also rewritten in a more idiomatic way, using `runBlocking` to wrap 
the execution of the main function:

<div class="sample" markdown="1" theme="idea">

```kotlin
fun main(args: Array<String>) = runBlocking { // start main coroutine
    GlobalScope.launch { // launch new coroutine in background and continue
        delay(1000L)
        println("World!")
    }
    println("Hello,") // main coroutine continues here immediately
    delay(2000L)      // delaying for 2 seconds to keep JVM alive
}
```

</div>

> You can get full code [here](../core/kotlinx-coroutines-core/test/guide/example-basic-02b.kt)

<!--- TEST
Hello,
World!
-->

Here `runBlocking<Unit> { ... }` works as an adaptor that is used to start the top-level main coroutine. 
We explicitly specify its `Unit` return type, because a well-formed `main` function in Kotlin has to return `Unit`.

This is also a way to write unit-tests for suspending functions:
 
<div class="sample" markdown="1" theme="idea">

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

<div class="sample" markdown="1" theme="idea">

```kotlin
fun main(args: Array<String>) = runBlocking {
    val job = GlobalScope.launch { // launch new coroutine and keep a reference to its Job
        delay(1000L)
        println("World!")
    }
    println("Hello,")
    job.join() // wait until child coroutine completes
}
```

</div>

> You can get full code [here](../core/kotlinx-coroutines-core/test/guide/example-basic-03.kt)

<!--- TEST
Hello,
World!
-->

Now the result is still the same, but the code of the main coroutine is not tied to the duration of
the background job in any way. Much better.

### Structured concurrency

There is still something to be desired for practical usage of coroutines. 
When we use `GlobalScope.launch` we create a top-level coroutine. Even though it is light-weight, it still 
consumes some memory resources while it runs. If we forget to keep a reference to the newly launched 
coroutine it still runs. What if the code in the coroutine hangs (for example, we erroneously
delay for too long), what if we launched too many coroutines and ran out of memory? 
Having to manually keep a reference to all the launched coroutines and [join][Job.join] them is error-prone. 

There is a better solution. We can use structured concurrency in our code. 
Instead of launching coroutines in the [GlobalScope], just like we usually do with threads (threads are always global), 
we can launch coroutines in the specific scope of the operation we are performing. 

In our example, we have `main` function that is turned into a coroutine using [runBlocking] coroutine builder.
Every coroutine builder, including `runBlocking`, adds an instance of [CoroutineScope] to the scope its code block. 
We can launch coroutines in this scope without having to `join` them explicitly, because
an outer coroutine (`runBlocking` in our example) does not complete until all the coroutines launched
in its scope complete. Thus, we can make our example simpler:

<div class="sample" markdown="1" theme="idea">

```kotlin
fun main(args: Array<String>) = runBlocking { // this: CoroutineScope
    launch { // launch new coroutine in the scope of runBlocking
        delay(1000L)
        println("World!")
    }
    println("Hello,")
}
```

</div>

> You can get full code [here](../core/kotlinx-coroutines-core/test/guide/example-basic-03s.kt)

<!--- TEST
Hello,
World!
-->

### Scope builder
In addition to the coroutine scope provided by different builders, it is possible to declare your own scope using
[coroutineScope] builder. It creates new coroutine scope and does not complete until all launched children
complete. The main difference between [runBlocking] and [coroutineScope] is that the latter does not block the current thread 
while waiting for all children to complete.

<div class="sample" markdown="1" theme="idea">

```kotlin
fun main(args: Array<String>) = runBlocking { // this: CoroutineScope
    launch { 
        delay(200L)
        println("Task from runBlocking")
    }
    
    coroutineScope { // Creates a new coroutine scope
        launch {
            delay(500L) 
            println("Task from nested launch")
        }
    
        delay(100L)
        println("Task from coroutine scope") // This line will be printed before nested launch
    }
    
    println("Coroutine scope is over") // This line is not printed until nested launch completes
}
```

</div>

> You can get full code [here](../core/kotlinx-coroutines-core/test/guide/example-basic-04.kt)

<!--- TEST
Task from coroutine scope
Task from runBlocking
Task from nested launch
Coroutine scope is over
-->

### Extract function refactoring

Let's extract the block of code inside `launch { ... }` into a separate function. When you 
perform "Extract function" refactoring on this code you get a new function with `suspend` modifier.
That is your first _suspending function_. Suspending functions can be used inside coroutines
just like regular functions, but their additional feature is that they can, in turn, 
use other suspending functions, like `delay` in this example, to _suspend_ execution of a coroutine.

<div class="sample" markdown="1" theme="idea">

```kotlin
fun main(args: Array<String>) = runBlocking {
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

> You can get full code [here](../core/kotlinx-coroutines-core/test/guide/example-basic-05.kt)

<!--- TEST
Hello,
World!
-->


But what if the extracted function contains a coroutine builder which is invoked on the current scope?
In this case `suspend` modifier on the extracted function is not enough. Making `doWorld` extension
method on `CoroutineScope` is one of the solutions, but it may not always be applicable as it does not make API clearer.
[currentScope] builder comes to help: it inherits current [CoroutineScope] from the coroutine context it is invoked.

<div class="sample" markdown="1" theme="idea">

```kotlin
fun main(args: Array<String>) = runBlocking {
    launchDoWorld()
    println("Hello,")
}

// this is your first suspending function
suspend fun launchDoWorld() = currentScope {
    launch {
        println("World!")
    }
}
```

</div>

> You can get full code [here](../core/kotlinx-coroutines-core/test/guide/example-basic-05s.kt)

<!--- TEST
Hello,
World!
-->

### Coroutines ARE light-weight

Run the following code:

<div class="sample" markdown="1" theme="idea">

```kotlin
fun main(args: Array<String>) = runBlocking {
    repeat(100_000) { // launch a lot of coroutines
        launch {
            delay(1000L)
            print(".")
        }
    }
}
```

</div>

> You can get full code [here](../core/kotlinx-coroutines-core/test/guide/example-basic-06.kt)

<!--- TEST lines.size == 1 && lines[0] == ".".repeat(100_000) -->

It launches 100K coroutines and, after a second, each coroutine prints a dot. 
Now, try that with threads. What would happen? (Most likely your code will produce some sort of out-of-memory error)

### Global coroutines are like daemon threads

The following code launches a long-running coroutine in [GlobalScope] that prints "I'm sleeping" twice a second and then 
returns from the main function after some delay:

<div class="sample" markdown="1" theme="idea">

```kotlin
fun main(args: Array<String>) = runBlocking {
    GlobalScope.launch {
        repeat(1000) { i ->
            println("I'm sleeping $i ...")
            delay(500L)
        }
    }
    delay(1300L) // just quit after delay
}
```

</div>

> You can get full code [here](../core/kotlinx-coroutines-core/test/guide/example-basic-07.kt)

You can run and see that it prints three lines and terminates:

```text
I'm sleeping 0 ...
I'm sleeping 1 ...
I'm sleeping 2 ...
```

<!--- TEST -->

Active coroutines that were launched in [GlobalScope] do not keep the process alive. They are like daemon threads.

<!--- MODULE kotlinx-coroutines-core -->
<!--- INDEX kotlinx.coroutines.experimental -->
[launch]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/launch.html
[CoroutineScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-coroutine-scope/index.html
[GlobalScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-global-scope/index.html
[delay]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/delay.html
[runBlocking]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/run-blocking.html
[Job]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-job/index.html
[Job.join]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-job/join.html
[coroutineScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/coroutine-scope.html
[currentScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/current-scope.html
<!--- END -->


