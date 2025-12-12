<contribute-url>https://github.com/Kotlin/kotlinx.coroutines/edit/master/docs/topics/</contribute-url>

[//]: # (title: Coroutines basics)

To create applications that perform multiple tasks at once, a concept known as concurrency,
Kotlin uses _coroutines_. A coroutine is a suspendable computation that lets you write concurrent code in a clear, sequential style.
Coroutines can run concurrently with other coroutines and potentially in parallel.

On the JVM and in Kotlin/Native, all concurrent code, such as coroutines, runs on _threads_, managed by the operating system.
Coroutines can suspend their execution instead of blocking a thread.
This allows one coroutine to suspend while waiting for some data to arrive and another coroutine to run on the same thread, ensuring effective resource utilization.

![Comparing parallel and concurrent threads](parallelism-and-concurrency.svg){width="700"}

For more information about the differences between coroutines and threads, see [Comparing coroutines and JVM threads](#comparing-coroutines-and-jvm-threads).

## Suspending functions

The most basic building block of coroutines is the _suspending function_.
It allows a running operation to pause and resume later without affecting the structure of your code.

To declare a suspending function, use the `suspend` keyword:

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

To include the `kotlinx.coroutines` library in your project, add the corresponding dependency configuration based on your build tool:

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

<tab title="Maven" group-key="maven">

```xml
<!-- pom.xml -->
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

</tab>
</tabs>


## Create your first coroutines

> The examples on this page use the explicit `this` expression with the coroutine builder functions `CoroutineScope.launch()` and `CoroutineScope.async()`.
> These coroutine builders are [extension functions](extensions.md) on `CoroutineScope`, and the `this` expression refers to the current `CoroutineScope` as the receiver.
>
> For a practical example, see [Extract coroutine builders from the coroutine scope](#extract-coroutine-builders-from-the-coroutine-scope).
>
{style="note"}

To create a coroutine in Kotlin, you need the following:

* A [suspending function](#suspending-functions).
* A [coroutine scope](#coroutine-scope-and-structured-concurrency) in which it can run, for example inside the `withContext()` function.
* A [coroutine builder](#coroutine-builder-functions) like `CoroutineScope.launch()` to start it.
* A [dispatcher](#coroutine-dispatchers) to control which threads it uses.

Let's look at an example that uses multiple coroutines in a multithreaded environment:

1. Import the `kotlinx.coroutines` library:

    ```kotlin
    import kotlinx.coroutines.*
    ```

2. Mark functions that can pause and resume with the `suspend` keyword:

    ```kotlin
    suspend fun greet() {
        println("The greet() on the thread: ${Thread.currentThread().name}")
    }
    
    suspend fun main() {}
    ```

    > While you can mark the `main()` function as `suspend` in some projects, it may not be possible when integrating with existing code or using a framework.
    > In that case, check the framework's documentation to see if it supports calling suspending functions.
    > If not, use [`runBlocking()`](#runblocking) to call them by blocking the current thread.
    > 
    {style="note"}

3. Add the [`delay()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/delay.html#) function to simulate a suspending task, such as fetching data or writing to a database:

    ```kotlin
    suspend fun greet() {
        println("The greet() on the thread: ${Thread.currentThread().name}")
        delay(1000L)
    }
   ```

    <!-- > Use [`kotlin.time.Duration`](https://kotlinlang.org/api/core/kotlin-stdlib/kotlin.time/-duration/) from the Kotlin standard library to express durations like `delay(1.seconds)` instead of using milliseconds.
    >
    {style="tip"} -->

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
   > By default, this pool uses up to as many threads as there are CPU cores available at runtime, with a minimum of two threads.
   > 
   > The coroutines launched inside the `withContext()` block share the same coroutine scope, which ensures [structured concurrency](#coroutine-scope-and-structured-concurrency).
   > 
   {style="note"}

5. Use a [coroutine builder function](#coroutine-builder-functions) like [`CoroutineScope.launch()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/launch.html) to start the coroutine:

    ```kotlin
    suspend fun main() {
        withContext(Dispatchers.Default) { // this: CoroutineScope
            // Starts a coroutine inside the scope with CoroutineScope.launch()
            this.launch { greet() }
            println("The withContext() on the thread: ${Thread.currentThread().name}")
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
        println("The greet() on the thread: ${Thread.currentThread().name}")
        // Suspends for 1 second and releases the thread
        delay(1.seconds) 
        // The delay() function simulates a suspending API call here
        // You can add suspending API calls here like a network request
    }

    suspend fun main() {
        // Runs the code inside this block on a shared thread pool
        withContext(Dispatchers.Default) { // this: CoroutineScope
            this.launch() {
                greet()
            }
   
            // Starts another coroutine
            this.launch() {
                println("The CoroutineScope.launch() on the thread: ${Thread.currentThread().name}")
                delay(1.seconds)
                // The delay function simulates a suspending API call here
                // You can add suspending API calls here like a network request
            }
    
            println("The withContext() on the thread: ${Thread.currentThread().name}")
        }
    }
    ```
    {kotlin-runnable="true"}

Try running the example multiple times. 
You may notice that the output order and thread names may change each time you run the program, because the OS decides when threads run.

> You can display coroutine names next to thread names in the output of your code for additional information.
> To do so, pass the `-Dkotlinx.coroutines.debug` VM option in your build tool or IDE run configuration.
>
> See [Debugging coroutines](https://github.com/Kotlin/kotlinx.coroutines/blob/master/docs/topics/debugging.md) for more information.
>
{style="tip"}

## Coroutine scope and structured concurrency

When you run many coroutines in an application, you need a way to manage them as groups.
Kotlin coroutines rely on a principle called _structured concurrency_ to provide this structure.

According to this principle, coroutines form a tree hierarchy of parent and child tasks with linked lifecycles.
A coroutine's lifecycle is the sequence of states from its creation until completion, failure, or cancellation.

A parent coroutine waits for its children to complete before it finishes.
If the parent coroutine fails or gets canceled, all its child coroutines are recursively canceled too.
Keeping coroutines connected this way makes cancellation and error handling predictable and safe.

To maintain structured concurrency, new coroutines can only be launched in a [`CoroutineScope`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-coroutine-scope/) that defines and manages their lifecycle.
The `CoroutineScope` includes the _coroutine context_, which defines the dispatcher and other execution properties.
When you start a coroutine inside another coroutine, it automatically becomes a child of its parent scope.

Calling a [coroutine builder function](#coroutine-builder-functions), such as `CoroutineScope.launch()` on a `CoroutineScope`, starts a child coroutine of the coroutine associated with that scope.
Inside the builder's block, the [receiver](lambdas.md#function-literals-with-receiver) is a nested `CoroutineScope`, so any coroutines you launch there become its children.

### Create a coroutine scope with the `coroutineScope()` function

To create a new coroutine scope with the current coroutine context, use the
[`coroutineScope()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/coroutine-scope.html) function.
This function creates a root coroutine of the coroutine subtree.
It's the direct parent of coroutines launched inside the block and the indirect parent of any coroutines they launch.
`coroutineScope()` executes the suspending block and waits until the block and any coroutines launched in it complete.

Here's an example:

```kotlin
// Imports the kotlin.time.Duration to express duration in seconds
import kotlin.time.Duration.Companion.seconds

import kotlinx.coroutines.*

// If the coroutine context doesn't specify a dispatcher,
// CoroutineScope.launch() uses Dispatchers.Default
//sampleStart
suspend fun main() {
    // Root of the coroutine subtree
    coroutineScope { // this: CoroutineScope
        this.launch {
            this.launch {
                delay(2.seconds)
                println("Child of the enclosing coroutine completed")
            }
            println("Child coroutine 1 completed")
        }
        this.launch {
            delay(1.seconds)
            println("Child coroutine 2 completed")
        }
    }
    // Runs only after all children in the coroutineScope have completed
    println("Coroutine scope completed")
}
//sampleEnd
```
{kotlin-runnable="true"}

Since no [dispatcher](#coroutine-dispatchers) is specified in this example, the `CoroutineScope.launch()` builder functions in the `coroutineScope()` block inherit the current context.
If that context doesn't have a specified dispatcher, `CoroutineScope.launch()` uses `Dispatchers.Default`, which runs on a shared pool of threads.

### Extract coroutine builders from the coroutine scope

In some cases, you may want to extract coroutine builder calls, such as [`CoroutineScope.launch()`](#coroutinescope-launch), into separate functions.

Consider the following example:

```kotlin
suspend fun main() {
    coroutineScope { // this: CoroutineScope
        // Calls CoroutineScope.launch() where CoroutineScope is the receiver
        this.launch { println("1") }
        this.launch { println("2") }
    } 
}
```

> You can also write `this.launch` without the explicit `this` expression, as `launch`.
> These examples use explicit `this` expressions to highlight that it's an extension function on `CoroutineScope`.
>
> For more information on how lambdas with receivers work in Kotlin, see [Function literals with receiver](lambdas.md#function-literals-with-receiver).
>
{style="tip"}

The `coroutineScope()` function takes a lambda with a `CoroutineScope` receiver.
Inside this lambda, the implicit receiver is a `CoroutineScope`, so builder functions like `CoroutineScope.launch()` and [`CoroutineScope.async()`](#coroutinescope-async) resolve as
[extension functions](extensions.md#extension-functions) on that receiver.

To extract the coroutine builders into another function, that function must declare a `CoroutineScope` receiver, otherwise a compilation error occurs:

```kotlin
import kotlinx.coroutines.*
//sampleStart
suspend fun main() {
    coroutineScope {
        launchAll()
    }
}

fun CoroutineScope.launchAll() { // this: CoroutineScope
    // Calls .launch() on CoroutineScope
    this.launch { println("1") }
    this.launch { println("2") } 
}
//sampleEnd
/* -- Calling launch without declaring CoroutineScope as the receiver results in a compilation error --

fun launchAll() {
    // Compilation error: this is not defined
    this.launch { println("1") }
    this.launch { println("2") }
}
 */
```
{kotlin-runnable="true"}

## Coroutine builder functions

A coroutine builder function is a function that accepts a `suspend` [lambda](lambdas.md) that defines a coroutine to run.
Here are some examples:

* [`CoroutineScope.launch()`](#coroutinescope-launch)
* [`CoroutineScope.async()`](#coroutinescope-async)
* [`runBlocking()`](#runblocking)
* [`withContext()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/with-context.html)
* [`coroutineScope()`](#create-a-coroutine-scope-with-the-coroutinescope-function)

Coroutine builder functions require a `CoroutineScope` to run in.
This can be an existing scope or one you create with helper functions such as `coroutineScope()`, [`runBlocking()`](#runblocking), or [`withContext()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/with-context.html#).
Each builder defines how the coroutine starts and how you interact with its result.

### `CoroutineScope.launch()`

The [`CoroutineScope.launch()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/launch.html#) coroutine builder function is an extension function on `CoroutineScope`.
It starts a new coroutine without blocking the rest of the scope, inside an existing [coroutine scope](#coroutine-scope-and-structured-concurrency).

Use `CoroutineScope.launch()` to run a task alongside other work when the result isn't needed or you don't want to wait for it:

```kotlin
// Imports the kotlin.time.Duration to enable expressing duration in milliseconds
import kotlin.time.Duration.Companion.milliseconds

import kotlinx.coroutines.*

suspend fun main() {
    withContext(Dispatchers.Default) {
        performBackgroundWork()
    }
}

//sampleStart
suspend fun performBackgroundWork() = coroutineScope { // this: CoroutineScope
    // Starts a coroutine that runs without blocking the scope
    this.launch {
        // Suspends to simulate background work
        delay(100.milliseconds)
        println("Sending notification in background")
    }

    // Main coroutine continues while a previous one suspends
    println("Scope continues")
}
//sampleEnd
```
{kotlin-runnable="true"}

After running this example, you can see that the `main()` function isn't blocked by `CoroutineScope.launch()` and keeps running other code while the coroutine works in the background.

> The `CoroutineScope.launch()` function returns a [`Job`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-job/) handle.
> Use this handle to wait for the launched coroutine to complete.
> For more information, see [Cancellation and timeouts](cancellation-and-timeouts.md#cancel-coroutines).
> 
{style="tip"}

### `CoroutineScope.async()`

The [`CoroutineScope.async()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/async.html) coroutine builder function is an extension function on `CoroutineScope`.
It starts a concurrent computation inside an existing [coroutine scope](#coroutine-scope-and-structured-concurrency) and returns a [`Deferred`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-deferred/) handle that represents an eventual result.
Use the `.await()` function to suspend the code until the result is ready:

```kotlin
// Imports the kotlin.time.Duration to enable expressing duration in milliseconds
import kotlin.time.Duration.Companion.milliseconds

import kotlinx.coroutines.*

//sampleStart
suspend fun main() = withContext(Dispatchers.Default) { // this: CoroutineScope
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
//sampleEnd
```
{kotlin-runnable="true"}

### `runBlocking()`

The [`runBlocking()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/run-blocking.html) coroutine builder function creates a coroutine scope and blocks the current [thread](#comparing-coroutines-and-jvm-threads) until
the coroutines launched in that scope finish.

Use `runBlocking()` only when there is no other option to call suspending code from non-suspending code:

```kotlin
import kotlin.time.Duration.Companion.milliseconds
import kotlinx.coroutines.*

// A third-party interface you can't change
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

A [_coroutine dispatcher_](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-dispatchers/#) controls which thread or thread pool coroutines use for their execution.
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
> You can specify a dispatcher to run a coroutine in a different context.
> 
> If the coroutine context doesn't include a dispatcher, coroutine builders use `Dispatchers.Default`.
>
{style="note"}

The `kotlinx.coroutines` library includes different dispatchers for different use cases.
For example, [`Dispatchers.Default`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-dispatchers/-default.html) runs coroutines on a shared pool of threads, performing work in the background,
separate from the main thread. This makes it an ideal choice for CPU-intensive operations like data processing.

To specify a dispatcher for a coroutine builder like `CoroutineScope.launch()`, pass it as an argument:

```kotlin
suspend fun runWithDispatcher() = coroutineScope { // this: CoroutineScope
    this.launch(Dispatchers.Default) {
        println("Running on ${Thread.currentThread().name}")
    }
}
```

Alternatively, you can use a `withContext()` block to run all code in it on a specified dispatcher:

```kotlin
// Imports the kotlin.time.Duration to enable expressing duration in milliseconds
import kotlin.time.Duration.Companion.milliseconds

import kotlinx.coroutines.*

//sampleStart
suspend fun main() = withContext(Dispatchers.Default) { // this: CoroutineScope
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
//sampleEnd
```
{kotlin-runnable="true"}

To learn more about coroutine dispatchers and their uses, including other dispatchers like [`Dispatchers.IO`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-dispatchers/-i-o.html) and [`Dispatchers.Main`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-dispatchers/-main.html), see [Coroutine context and dispatchers](coroutine-context-and-dispatchers.md).

## Comparing coroutines and JVM threads

While coroutines are suspendable computations that run code concurrently like threads on the JVM, they work differently under the hood.

A _thread_ is managed by the operating system. Threads can run tasks in parallel on multiple CPU cores and represent a standard approach to concurrency on the JVM.
When you create a thread, the operating system allocates memory for its stack and uses the kernel to switch between threads.
This makes threads powerful but also resource-intensive.
Each thread usually needs a few megabytes of memory, and typically the JVM can only handle a few thousand threads at once.

On the other hand, a coroutine isn't bound to a specific thread.
It can suspend on one thread and resume on another, so many coroutines can share the same thread pool.
When a coroutine suspends, the thread isn't blocked and remains free to run other tasks.
This makes coroutines much lighter than threads and allows running millions of them in one process without exhausting system resources.

![Comparing coroutines and threads](coroutines-and-threads.svg){width="700"}

Let's look at an example where 50,000 coroutines each wait five seconds and then print a period (`.`):

```kotlin
import kotlin.time.Duration.Companion.seconds
import kotlinx.coroutines.*

suspend fun main() {
    withContext(Dispatchers.Default) {
        // Launches 50,000 coroutines that each wait five seconds, then print a period
        printPeriods()
    }
}

//sampleStart
suspend fun printPeriods() = coroutineScope { // this: CoroutineScope
    // Launches 50,000 coroutines that each wait five seconds, then print a period
    repeat(50_000) {
        this.launch {
            delay(5.seconds)
            print(".")
        }
    }
}
//sampleEnd
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
{kotlin-runnable="true" validate="false"}

Running this version uses much more memory because each thread needs its own memory stack.
For 50,000 threads, that can be up to 100 GB, compared to roughly 500 MB for the same number of coroutines.

Depending on your operating system, JDK version, and settings,
the JVM thread version may throw an out-of-memory error or slow down thread creation to avoid running too many threads at once.

## What's next

* Discover more about combining suspending functions in [Composing suspending functions](composing-suspending-functions.md).
* Learn how to cancel coroutines and handle timeouts in [Cancellation and timeouts](cancellation-and-timeouts.md).
* Dive deeper into coroutine execution and thread management in [Coroutine context and dispatchers](coroutine-context-and-dispatchers.md).
* Learn how to return multiple asynchronously computed values in [Asynchronous flows](flow.md).

