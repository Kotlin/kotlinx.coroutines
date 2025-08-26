<contribute-url>https://github.com/Kotlin/kotlinx.coroutines/edit/master/docs/topics/</contribute-url>

[//]: # (title: Coroutines basics)

To create applications that perform multiple tasks at once, a concept known as concurrency,
Kotlin uses coroutines. Coroutines let you write concurrent code in a clear and sequential style.

The most basic building block of coroutines is the suspending function.
It makes it possible to pause a running operation and resume it later without losing the structure of your code.

To mark a function as a suspending function, use the `suspend` keyword:

```kotlin
suspend fun greet() {
    println("Hello world from a suspending function")
}
```

You can only call a suspending function from another suspending function.
To call suspending functions at the entry point of a Kotlin application, mark the `main()` function with the `suspend` keyword:

```kotlin
suspend fun main() {
    showUserInfo()
}

suspend fun showUserInfo() {
    println("Loading user...")
    greet()
    println("User: John Smith")
}

suspend fun greet() {
    println("Hello world from a suspending function")
}
```
{kotlin-runnable="true"}

This example doesn't use concurrency yet, but by marking the functions with the `suspend` keyword,
you allow them to call other suspending functions and run concurrent code inside.

While the `suspend` keyword is part of the core Kotlin language, most coroutine features
are available through the [`kotlinx.coroutines`](https://github.com/Kotlin/kotlinx.coroutines) library.

## Add the kotlinx.coroutines library to your project

To include the `kotlinx.coroutines` library in your project, add the corresponding dependency configuration based on your build tool.

### Gradle

Add the following dependency to your `build.gradle(.kts)` file:

<tabs group="build-tool">
<tab title="Kotlin" group-key="kotlin">

```kotlin
// build.gradle.kts
repositories {
    mavenCentral()
}

dependencies {
    implementation("org.jetbrains.kotlinx:kotlinx-coroutines-core:%coroutinesVersion%")
}
```

</tab>
<tab title="Groovy" group-key="groovy">

```groovy
// build.gradle
repositories {
    mavenCentral()
}

dependencies {
    implementation 'org.jetbrains.kotlinx:kotlinx-coroutines-core:%coroutinesVersion%'
}
```
</tab>
</tabs>

### Maven

Add the following dependency to your `pom.xml` file.

```xml
<project>
    <dependencies>
        <dependency>
            <groupId>org.jetbrains.kotlinx</groupId>
            <artifactId>kotlinx-coroutines-core</artifactId>
            <version>%coroutinesVersion%</version>
        </dependency>
    </dependencies>
    ...
</project>
```

## Create your first coroutines

> The examples on this page use the explicit `this` expression with the coroutine builder functions `CoroutineScope.launch()` and `CoroutineScope.async()`.
> These coroutine builders are extension functions on `CoroutineScope`, and the `this` expression refers to the current `CoroutineScope` as the receiver.
>
> For a practical example, see [Extract coroutine builders from the coroutine scope](#extract-coroutine-builders-from-the-coroutine-scope).
>
{style="note"}

A coroutine is a suspendable computation that can run concurrently with other coroutines and potentially in parallel.

On the JVM and in Kotlin/Native, all concurrent code, such as coroutines, runs on _threads_, which are managed by the operating system.
Coroutines can suspend their execution instead of blocking a thread.
This allows one coroutine to suspend while waiting for some data to arrive and another coroutine to run on the same thread, ensuring effective resource utilization.

![Comparing parallel and concurrent threads](parallelism-and-concurrency.svg){width="700"}

To create a coroutine in Kotlin, you need the following:

* A suspending function.
* A coroutine scope in which it can run, such as one available inside the `withContext()` function.
* A coroutine builder like `CoroutineScope.launch()` to start it.
* A dispatcher to control which threads it uses. 

> You can display coroutine names next to thread names in the output of your code for additional information.
> To do so, pass the `-Dkotlinx.coroutines.debug` VM option in your build tool or IDE run configuration.
>
> See [Debugging coroutines](https://github.com/Kotlin/kotlinx.coroutines/blob/master/docs/topics/debugging.md) for more information.
>
{style="tip"}

Let's look at an example that uses multiple coroutines in a multithreaded environment:

1. Import the `kotlinx.coroutines` library:

    ```kotlin
    import kotlinx.coroutines.*
    ```

2. Mark functions that can pause and resume with the `suspend` keyword:

    ```kotlin
    suspend fun greet() {
        println("Hello world from a suspending function on thread: ${Thread.currentThread().name}")
    }
    
    suspend fun main() {}
    ```

    > While you can mark the `main()` function as `suspend` in some projects, it may not be possible when integrating with existing code or using a framework.
    > In that case, check the framework's documentation to see if it supports calling suspending functions.
    > If not, use [`runBlocking`](#runblocking) to call them by blocking the current thread.
    > 
    {style="note"}

3. Add the [`delay()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/delay.html#) function to simulate a suspending task, such as fetching data or writing to a database:

    ```kotlin
    suspend fun greet() {
        println("Hello world from a suspending function on thread: ${Thread.currentThread().name}")
        delay(1000L)
    }
   ```

    > Use [`kotlin.time.Duration`](https://kotlinlang.org/api/core/kotlin-stdlib/kotlin.time/-duration/) from the Kotlin standard library to express durations like `delay(1.seconds)` instead of using milliseconds.
    >
    {style="tip"}

4. Use [`withContext(Dispatchers.Default)`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/with-context.html#) to define an entry point for multithreaded concurrent code that runs on a shared thread pool:

    ```kotlin
    suspend fun main() {
        withContext(Dispatchers.Default) {
            // Add the coroutine builders here
        }
    }
    ```

   > The suspending `withContext()` function is typically used for [context switching](coroutine-context-and-dispatchers.md#jumping-between-threads), but in this example,
   > it also defines a non-blocking entry point for concurrent code.
   > It uses the [`Dispatchers.Default` dispatcher](#coroutine-dispatchers) to run code on a shared thread pool for multithreaded execution.
   > 
   > The coroutines launched inside the `withContext()` block share the same coroutine scope, which ensures [structured concurrency](#coroutine-scope-and-structured-concurrency).
   > 
   {style="note"}

5. Use a [coroutine builder function](#coroutine-builder-functions) like [`CoroutineScope.launch()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/launch.html) to start the coroutine:

    ```kotlin
    suspend fun main() {
        withContext(Dispatchers.Default) {
            // Starts a coroutine inside the scope with CoroutineScope.launch()
            this.launch { greet() }
            println("This runs concurrently and possibly in parallel with the launched coroutines on thread: ${Thread.currentThread().name}")
        }
    }
    ```

6. Combine these pieces to run multiple coroutines at the same time on a shared pool of threads:

    ```kotlin
    // Imports the coroutines library
    import kotlinx.coroutines.*

    // Imports the kotlin.time.Duration to express duration in seconds
    import kotlin.time.Duration.Companion.seconds

    // Defines a suspending function
    suspend fun greet() {
        println("Hello from greet() on thread: ${Thread.currentThread().name}")
        // Delays for 1 second
        delay(1.seconds) 
        // The delay function simulates a suspending API call here
        // You can add suspending API calls here like a network request
    }

    suspend fun main() {
        // Runs all concurrent code on a shared thread pool
        withContext(Dispatchers.Default) {
            this.launch() {
                greet()
            }
   
            // Starts another coroutine
            this.launch() {
                println("Another coroutine on thread: ${Thread.currentThread().name}")
                delay(1.seconds)
                // The delay function simulates a suspending API call here
                // You can add suspending API calls here like a network request
            }
    
            println("This runs concurrently and possibly in parallel with the launched coroutines on thread: ${Thread.currentThread().name}")
        }
    }
    ```
    {kotlin-runnable="true"}

This example demonstrates simple multithreading with coroutines on a shared thread pool.

> Try running the example multiple times. 
> You may notice that the output order and thread names may change each time you run the program. 
> This is because the OS decides when threads run and tasks complete.
> 
{style="tip"}

## Coroutine scope and structured concurrency

When you run many coroutines in an application, you need a way to manage them as groups.
Kotlin coroutines rely on a principle called _structured concurrency_ to provide this structure.

This principle groups coroutines into a hierarchy of parent and child tasks with linked lifecycles.
Coroutines form a tree hierarchy where each coroutine has at most one parent and can have any number of children.
A parent coroutine waits for its children to complete before it completes.
If the parent coroutine fails or is canceled, all its child coroutines are canceled too.
Keeping coroutines connected this way makes cancellation, error handling, and resource cleanup predictable and safe.

> A coroutine's lifecycle is the period from its creation until it completes, fails, or is canceled.
>
{style="tip"}

To maintain structured concurrency, new coroutines can only be launched in a [`CoroutineScope`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-coroutine-scope/) that defines and manages their lifecycle.
When you start a coroutine inside another coroutine, it automatically becomes a child of its parent scope.
The parent coroutine's scope waits for all its children to finish before it completes.

Calling a [coroutine builder function](#coroutine-builder-functions) such as `CoroutineScope.launch()` on a `CoroutineScope` starts a child coroutine of the coroutine associated with that scope.
Inside the builder's block, the [receiver](lambdas.md#function-literals-with-receiver) is a `CoroutineScope`, so any coroutines you launch there become its children.
I don't want to be too explicit here. I want to explain this further down in the next section. 

While you can use the `withContext()` function to create a scope for your coroutines,
you can use the [`coroutineScope()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/coroutine-scope.html) function when you want to create a new coroutine scope without changing the context.
It executes the suspending block inline and waits until the block and any coroutines launched in it complete.

Here's an example:

```kotlin
// Imports the kotlin.time.Duration to express duration in seconds
import kotlin.time.Duration.Companion.seconds

import kotlinx.coroutines.*

suspend fun main() {
    println("Starting coroutine scope")
    coroutineScope {
        this.launch {
            delay(1.seconds)
            coroutineScope {
                this.launch {
                    delay(2.seconds)
                    println("The nested coroutine completed")
                }
            }
            println("The first coroutine completed")
        }
        this.launch {
            delay(2.seconds)
            println("The second coroutine completed")
        }
    }

    // Runs only after all children in the coroutineScope have completed
    println("Coroutine scope completed")
}
```
{kotlin-runnable="true"}

This example uses the [`delay()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/delay.html#) function to show how the coroutine scope waits for its child coroutines to finish.
Since no [dispatcher](#coroutine-dispatchers) is specified here, the `CoroutineScope.launch()` calls in the `coroutineScope()` block inherit the current context.
If that context doesn't have a specified dispatcher, coroutine builders use `Dispatchers.Default`, which runs on a shared pool of threads.

### Extract coroutine builders from the coroutine scope

The `coroutineScope()` function takes a lambda with a `CoroutineScope` receiver.
Inside this lambda, the implicit receiver is a `CoroutineScope`, so builder functions like `CoroutineScope.launch()` and `.async()` resolve as
[extension functions](extensions.md#extension-functions) on that receiver:

```kotlin
suspend fun main() = coroutineScope { // this: CoroutineScope
    // Calls CoroutineScope.launch() where CoroutineScope is the receiver
    this.launch { println("1") }
    this.launch { println("2") }
}
```

> For more information on how lambdas with receivers work in Kotlin, see [Function literals with receiver](lambdas.md#function-literals-with-receiver).
>
{style="tip"}

To extract the coroutine builders into another function, that function must declare a `CoroutineScope` receiver:

```kotlin
suspend fun main() {
    coroutineScope { // this: CoroutineScope #1
        // launchAll() creates its own child CoroutineScope
        launchAll()
    } 
}

// Doesn't declare CoroutineScope as the receiver
suspend fun launchAll() {
    // Error: unresolved reference launch()
    this.launch { println("1") }
    this.launch { println("2") }
}

// Creates a new CoroutineScope as the receiver for the .launch() coroutine builders
suspend fun launchAll() = coroutineScope { // this: CoroutineScope #2
    // Calls .launch() on CoroutineScope #2
    this.launch { println("1") }
    this.launch { println("2") } 
}
```

## Coroutine builder functions

A coroutine builder function is a function that accepts a `suspend` [lambda](lambdas.md) that defines a coroutine to run.
This includes the following:

* [`CoroutineScope.launch()`](#coroutinescope-launch)
* [`CoroutineScope.async()`](#coroutinescope-async)
* [`runBlocking()`](#runblocking)
* `withContext()`
* `coroutineScope()`

Coroutine builder functions create new coroutines inside an existing [coroutine scope](#coroutine-scope-and-structured-concurrency).
They require a `CoroutineScope` to run in, either one that is already available,
or one you create using helper functions such as `coroutineScope()`, [`runBlocking()`](#runblocking), or [`withContext()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/with-context.html#).
Each builder defines how the coroutine starts and how you interact with its result.

### CoroutineScope.launch()

The [`CoroutineScope.launch()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/launch.html#) coroutine builder function is an extension function on `CoroutineScope`.
It starts a new coroutine without blocking the rest of the scope.
Use `CoroutineScope.launch()` to run a task alongside other work when the result isn't needed or you don't want to wait for it:

```kotlin
// Imports the kotlin.time.Duration to enable expressing duration in milliseconds
import kotlin.time.Duration.Companion.milliseconds

import kotlinx.coroutines.*

suspend fun main() = coroutineScope {
    // Starts a coroutine that runs without blocking the scope
    this.launch {
        // Delays to simulate background work
        delay(100.milliseconds)
        println("Sending notification in background")
    }

    // Main coroutine continues while a previous one is delayed
    println("Scope continues")
}
```
{kotlin-runnable="true"}

After running this example, you can see that the `main()` function isn't blocked by `CoroutineScope.launch()` and keeps running other code while the coroutine works in the background.

> The `CoroutineScope.launch()` function returns a [`Job`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-job/) handle.
> Use this handle to wait for the launched coroutine to complete.
> For more information, see [Cancellation and timeouts](cancellation-and-timeouts.md#cancelling-coroutine-execution)
> 
{style="tip"}

### CoroutineScope.async()

The [`CoroutineScope.async()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/async.html) coroutine builder function is an extension function on `CoroutineScope`.
It starts a concurrent computation and returns a [`Deferred`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-deferred/) handle that represents an eventual result.
Use the `.await()` function to suspend the code until the result is ready:

```kotlin
// Imports the kotlin.time.Duration to enable expressing duration in milliseconds
import kotlin.time.Duration.Companion.milliseconds

import kotlinx.coroutines.*

suspend fun main() = withContext(Dispatchers.Default) {
   // Starts downloading the first page
   val firstPage = this.async {
      delay(50.milliseconds)
      "First page"
   }

   // Starts downloading the second page in parallel
   val secondPage = this.async {
      delay(100.milliseconds)
      "Second page"
   }

   // Awaits both results and compares them
   val pagesAreEqual = firstPage.await() == secondPage.await()
   println("Pages are equal: $pagesAreEqual")
}
```
{kotlin-runnable="true"}

### runBlocking()

The [`runBlocking()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/run-blocking.html) coroutine builder function creates a coroutine scope and blocks the current [thread](#comparing-coroutines-and-jvm-threads) until
the coroutines launched in that scope finish.

Use `runBlocking()` only when there is no other option to call suspending code from non-suspending code:

```kotlin
// Imports the kotlin.time.Duration to enable expressing duration in milliseconds
import kotlin.time.Duration.Companion.milliseconds

import kotlinx.coroutines.*

// A third-party interface we cannot change
interface Repository {
    fun readItem(): Int
}

object MyRepository : Repository {
    override fun readItem(): Int {
        // Bridges to a suspending function
        return runBlocking {
            myReadItem()
        }
    }
}

suspend fun myReadItem(): Int {
    delay(100.milliseconds)
    return 4
}
```

## Coroutine dispatchers

A [coroutine dispatcher](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-dispatchers/#) controls which thread or thread pool coroutines use for their execution.
Coroutines aren't always tied to a single thread.
They can pause on one thread and resume on another, depending on the dispatcher.
This lets you run many coroutines at the same time without allocating a separate thread for every coroutine.

> Even though coroutines can suspend and resume on different threads,
> values written before the coroutine suspends are still guaranteed to be available within the same coroutine when it resumes.
>
{style="tip"}

A dispatcher works together with the [coroutine scope](#coroutine-scope-and-structured-concurrency) to define when coroutines run and where they run.
While the coroutine scope controls the coroutine's lifecycle, the dispatcher controls which threads are used for execution.

> You don't have to specify a dispatcher for every coroutine.
> By default, coroutines inherit the dispatcher from their parent scope.
> You can specify a dispatcher if you need to run a coroutine in a different context.
> 
> If the coroutine context doesn't include a dispatcher, coroutine builders use `Dispatchers.Default`.
>
{style="note"}

The `kotlinx.coroutines` library includes different dispatchers for different use cases.
For example, [`Dispatchers.Default`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-dispatchers/-default.html) runs coroutines on a shared pool of threads performing work in the background,
separate from the main thread.

To specify a dispatcher for a coroutine builder like `CoroutineScope.launch()`, pass it as an argument:

```kotlin
suspend fun runWithDispatcher() = coroutineScope {
    this.launch(Dispatchers.Default) {
        println("Running on ${Thread.currentThread().name}")
    }
}
```

Alternatively, you can use a `withContext()` block to run all code in it on a specified dispatcher.

The following example runs on `Dispatchers.Default`, which is optimized for CPU-intensive operations like data processing:

```kotlin
// Imports the kotlin.time.Duration to enable expressing duration in milliseconds
import kotlin.time.Duration.Companion.milliseconds

import kotlinx.coroutines.*

suspend fun main() = withContext(Dispatchers.Default) {
    println("Running withContext block on ${Thread.currentThread().name}")

    val one = this.async {
        println("First calculation starting on ${Thread.currentThread().name}")
        val sum = (1L..500_000L).sum()
        delay(200L)
        println("First calculation done on ${Thread.currentThread().name}")
        sum
    }

    val two = this.async {
        println("Second calculation starting on ${Thread.currentThread().name}")
        val sum = (500_001L..1_000_000L).sum()
        println("Second calculation done on ${Thread.currentThread().name}")
        sum
    }

    // Waits for both calculations and prints the result
    println("Combined total: ${one.await() + two.await()}")
}
```
{kotlin-runnable="true"}

To learn more about coroutine dispatchers and their uses, including other dispatchers like [`Dispatchers.IO`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-dispatchers/-i-o.html) and [`Dispatchers.Main`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-dispatchers/-main.html), see [Coroutine context and dispatchers](coroutine-context-and-dispatchers.md).

## Comparing coroutines and JVM threads

While coroutines are suspendable computations that run code concurrently like threads on the JVM, they work differently under the hood.

A _thread_ is managed by the operating system. Threads can run tasks parallel on multiple CPU cores and represent a standard approach to concurrency on the JVM.
When you create a thread, the operating system allocates memory for its stack and uses the kernel to switch between threads.
This makes threads powerful but also resource-intensive.
Each thread usually needs a few megabytes of memory, and typically the JVM can only handle a few thousand threads at once.

On the other hand, a coroutine isn't bound to a specific thread.
It can suspend on one thread and resume on another, so many coroutines can share the same thread pool.
When a coroutine suspends, the thread isn't blocked, and it remains free to run other tasks.
This makes coroutines much lighter than threads and allows running millions in one process without exhausting system resources.

![Comparing coroutines and threads](coroutines-and-threads.svg){width="700"}

Let's look at an example where 50,000 coroutines each wait five seconds and then print a period (`.`):

```kotlin
// Imports the kotlin.time.Duration to express duration in seconds
import kotlin.time.Duration.Companion.seconds

import kotlinx.coroutines.*

suspend fun main() = coroutineScope {
    // Launches 50,000 coroutines that each wait five seconds, then print a period
    repeat(50_000) {
        this.launch {
            delay(5.seconds)
            print(".")
        }
    }
}
```
{kotlin-runnable="true" kotlin-min-compiler-version="1.3"}

Now let's look at the same example using JVM threads:

```kotlin
import kotlin.concurrent.thread

fun main() {
    repeat(50_000) {
        thread {
            Thread.sleep(5000L)
            print(".")
        }
    }
}
```

Running this version uses much more memory because each thread needs its own memory stack.
For 50,000 threads, that can be up to 100 GB, compared to roughly 500 MB for the same number of coroutines.

Depending on your operating system, JDK version, and settings,
the JVM thread version may either throw an out-of-memory error or slow down thread creation to avoid running too many threads at once.

## What's next

* Discover more about combining suspending functions in [Composing suspending functions](composing-suspending-functions.md).
* Learn how to cancel coroutines and handle timeouts in [Cancellation and timeouts](cancellation-and-timeouts.md).
* Dive deeper into coroutine execution and thread management in [Coroutine context and dispatchers](coroutine-context-and-dispatchers.md).
* Learn how to return multiple asynchronously computed values in [Asynchronous flows](flow.md)
