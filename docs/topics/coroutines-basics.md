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
            <groupId>org.jetbrains.kotlin</groupId>
            <artifactId>kotlinx-coroutines-core</artifactId>
            <version>%coroutinesVersion%</version>
        </dependency>
    </dependencies>
    ...
</project>
```

## Create your first coroutines

Suspending functions are the basic building blocks for concurrency in Kotlin.
A coroutine is a suspendable computation that can run concurrently with other coroutines and potentially in parallel.

On the JVM and in Kotlin/Native, all concurrent code, such as coroutines, runs on _threads_, which are managed by the operating system.
Coroutines can suspend their execution instead of blocking a thread.
This allows one coroutine to suspend while waiting for a network response and another to run on the same thread, ensuring effective resource utilization.

![Comparing parallel and concurrent threads](parallelism-and-concurrency.svg){width="700"}

To create a coroutine in Kotlin, you need the following:

* A suspending function.
* A coroutine scope in which it can run, such as one available inside the `withContext()` function.
* A coroutine builder like `.launch()` to start it.
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
    > In that case, check the framework’s documentation to see if it supports calling suspending functions.
    > If not, use [`runBlocking`](#runblocking) to call them by blocking the current thread.
    > 
    {style="note"}


3. Use [`withContext(Dispatchers.Default)`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/with-context.html#) to define a safe entry point for multithreaded concurrent code that runs on a shared thread pool:

    ```kotlin
    suspend fun main() = withContext(Dispatchers.Default) {
        // Add the coroutine builders here
    }
    ```

   > The `withContext()` function is typically used for [context switching](coroutine-context-and-dispatchers.md#jumping-between-threads), but in this example,
   > it also defines a safe entry point for concurrent code.
   > It uses the [`Dispatchers.Default` dispatcher](#coroutine-dispatchers) to run code on a shared thread pool for multithreaded execution.
   > 
   > The coroutines launched inside the `withContext()` block share the same coroutine scope, which ensures [structured concurrency](#coroutine-scope-and-structured-concurrency).
   > 
   {style="note"}

4. Use a [coroutine builder function](#coroutine-builder-functions) like [`.launch()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/launch.html) to start the coroutine:

    ```kotlin
    suspend fun main() = withContext(Dispatchers.Default) {
        // Starts a coroutine inside the scope
        launch { greet() }
        println("This runs concurrently and possibly in parallel with the launched coroutines on thread: ${Thread.currentThread().name}")
    }
    ```

5. Combine these pieces to run multiple coroutines at the same time on a shared pool of threads:

    ```kotlin
    // Imports the coroutines library
    import kotlinx.coroutines.*
    
    // Defines a suspending function
    suspend fun greet() {
        println("Hello from greet() on thread: ${Thread.currentThread().name}")
    }
    
    // Runs all concurrent code on a shared thread pool
    suspend fun main() = withContext(Dispatchers.Default) {
        launch() {
            greet()
        }
   
        // Starts another coroutine
        launch() {
            println("Another coroutine on thread: ${Thread.currentThread().name}")
        }
    
        println("This runs concurrently and possibly in parallel with the launched coroutines on thread: ${Thread.currentThread().name}")
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

When you run many coroutines in an application, you need a way to manage them as a group.
Kotlin coroutines rely on a principle called _structured concurrency_ to provide this structure.

This principle connects coroutines into a hierarchy of parent and child tasks that share the same lifecycle.
A parent coroutine waits for its children to complete before finishing.
If the parent coroutine fails or is canceled, all its child coroutines are canceled too.
Keeping coroutines connected this way makes cancellation, error handling, and resource cleanup predictable and safe.

> A coroutine’s lifecycle is the period from its start until it completes, fails, or is canceled.
>
{style="tip"}

To maintain structured concurrency, new coroutines can only be launched in a [`CoroutineScope`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-coroutine-scope/) that defines and manages their lifecycle.

[Coroutine builder functions](#coroutine-builder-functions) are extension functions on `CoroutineScope`.
When you start a coroutine inside another coroutine, it automatically becomes a child of its parent scope.
The parent coroutine's scope waits for all its children to finish before it completes.

To create a coroutine scope without launching a new coroutine, use the [`coroutineScope()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/coroutine-scope.html) function:

```kotlin
// Imports the kotlin.time.Duration to express duration in seconds
import kotlin.time.Duration.Companion.seconds

import kotlinx.coroutines.*

suspend fun main() {
    println("Starting coroutine scope")
    coroutineScope {
        launch {
            delay(1.seconds)
            println("The first coroutine completed")
        } 
        launch {
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
You can specify the wait time in milliseconds, so `delay(1000L)` suspends the coroutine for one second without blocking the thread.

> Use [`kotlin.time.Duration`](https://kotlinlang.org/api/core/kotlin-stdlib/kotlin.time/-duration/) from the Kotlin standard library to express durations like `delay(1.seconds)` instead of using milliseconds.
> 
{style="tip"}

### Extract coroutine builders from the coroutine scope

The `coroutineScope()` function takes a lambda with a `CoroutineScope` receiver.
Inside this lambda, you can call coroutine builder functions like `.launch()` and `.async()` because they are extension
functions on `CoroutineScope`.

```kotlin
suspend fun main() = coroutineScope {
    launch { println("1") }
    launch { println("2") }
}
```

To extract the coroutine builders into another function, that function must declare a `CoroutineScope` receiver:

```kotlin
suspend fun main() = coroutineScope {
    // Calls this.launchAll() on the CoroutineScope receiver
    launchAll()
}

// Doesn't declare CoroutineScope as the receiver
suspend fun launchAll() {
    // Error: 'launch' is unresolved
    launch { println("1") }
    launch { println("2") }
}

// Declares CoroutineScope as the receiver
suspend fun CoroutineScope.launchAll() {
   launch { println("1") }
   launch { println("2") }
}
```

For more information on how lambdas with receivers work in Kotlin, see [Function literals with receiver](lambdas.md#function-literals-with-receiver).

## Coroutine builder functions

Coroutine builder functions create new coroutines inside an existing [coroutine scope](#coroutine-scope-and-structured-concurrency).
They require a `CoroutineScope` to run in, either one that is already available,
or one you create using helper functions such as `coroutineScope()` or [`runBlocking()`](#runblocking).
Each builder defines how the coroutine starts and how you interact with its result.

> The `withContext()` function doesn't create a new scope but provides access to the current one.
> 
{style="tip"}

### .launch()

The [`.launch()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/launch.html#) coroutine builder function starts a new coroutine without blocking the rest of the scope.
Use `.launch()` to run a task alongside other work when the result isn't needed or you don't want to wait for it:

```kotlin
// Imports the kotlin.time.Duration to enable expressing duration in milliseconds
import kotlin.time.Duration.Companion.milliseconds

import kotlinx.coroutines.*

suspend fun main() = coroutineScope {
    // Starts a coroutine that runs without blocking the scope
    launch {
        // Delays to simulate background work
        delay(100.milliseconds)
        println("Sending notification in background")
    }

    // Main coroutine continues while a previous one is delayed
    println("Scope continues")
}
```
{kotlin-runnable="true"}

After running this example, you can see that the `main()` function isn't blocked by `.launch()` and keeps running other code while the coroutine works in the background.

### .async()

Use the [`.async()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/async.html) builder function to start an asynchronous computation that runs alongside other code and returns a result you can access later.
The result is wrapped in a [`Deferred`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-deferred/) object, which you can access by calling the `.await()` function:

```kotlin
// Imports the kotlin.time.Duration to enable expressing duration in milliseconds
import kotlin.time.Duration.Companion.milliseconds

import kotlinx.coroutines.*

suspend fun main() = withContext(Dispatchers.Default) {
   // Starts downloading the first page
   val firstPage = async {
      delay(50.milliseconds)
      "First page"
   }

   // Starts downloading the second page in parallel
   val secondPage = async {
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

The [`runBlocking()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/run-blocking.html) coroutine builder function creates coroutine scope and blocks the current [thread](#comparing-coroutines-and-jvm-threads) until
the coroutines launched in that scope finish.
Unlike other coroutine builders, `runBlocking()` doesn't use a shared thread pool.

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
        // Bridges to a suspending function safely
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

A dispatcher works together with the [coroutine scope](#coroutine-scope-and-structured-concurrency) to define when coroutines run and where they run.
While the coroutine scope controls the coroutine's lifecycle, the dispatcher controls which threads are used for execution.

> You don't have to specify a dispatcher for every coroutine.
> By default, coroutines inherit the dispatcher from their parent scope.
> You can specify a dispatcher if you need to run a coroutine in a different context.
>
{style="note"}

The `kotlinx.coroutines` library includes different dispatchers for different use cases.
For example, [`Dispatchers.Default`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-dispatchers/-default.html) runs coroutines on a shared pool of threads performing work in the background,
separate from the main thread.

To specify a dispatcher for a coroutine builder like `.launch()`, pass it as an argument:

```kotlin
suspend fun runWithDispatcher() = coroutineScope {
    launch(Dispatchers.Default) {
        println("Running on ${Thread.currentThread().name}")
    }
}
```

Alternatively, you can wrap multiple coroutines in a `withContext()` block to apply a dispatcher to all of them.

The following example runs on `Dispatchers.Default`, which is optimized for CPU-intensive operations like data processing:

```kotlin
// Imports the kotlin.time.Duration to enable expressing duration in milliseconds
import kotlin.time.Duration.Companion.milliseconds

import kotlinx.coroutines.*

suspend fun main() = withContext(Dispatchers.Default) {
   println("Running withContext block on ${Thread.currentThread().name}")

   val one = async {
      println("First calculation starting on ${Thread.currentThread().name}")
      val sum = (1..500_000).sum()
      delay(200L)
      println("First calculation done on ${Thread.currentThread().name}")
      sum
   }

   val two = async {
      println("Second calculation starting on ${Thread.currentThread().name}")
      val sum = (500_001..1_000_000).sum()
      println("Second calculation done on ${Thread.currentThread().name}")
      sum
   }

   // Waits for both calculations and prints the result
   println("Combined total: ${one.await() + two.await()}")
}
```
{kotlin-runnable="true"}

> Even though coroutines can suspend and resume on different threads,
> values written before the coroutine suspends are still available within the same coroutine when it resumes.
> 
{style="tip"}

For more information, see [Coroutine context and dispatchers](coroutine-context-and-dispatchers.md)

## Comparing coroutines and JVM threads

While coroutines are suspendable computations that run code concurrently like threads on the JVM, they work differently under the hood.

A _thread_ is managed by the operating system. Threads can run tasks parallel on multiple CPU cores and represent a standard approach to concurrency on the JVM.
When you create a thread, the operating system allocates memory for its stack and uses the kernel to switch between threads.
This makes threads powerful but also resource-intensive.
Each thread usually needs a few megabytes of memory, and typically the JVM can only handle a few thousand threads at once.

On the other hand, a coroutine isn't bound to a specific thread.
It can suspend on one thread and resume on another, so many coroutines can share the same thread pool.
When a coroutine suspends, the thread isn't blocked, and it remains free to run other tasks.
This makes coroutines much lighter than threads and allows running hundreds of thousands in one process without exhausting system resources.

![Comparing coroutines and threads](coroutines-and-threads.svg){width="700"}

Let's look at an example where 50,000 coroutines each wait five seconds and then print a period (`.`):

```kotlin
// Imports the kotlin.time.Duration to express duration in seconds
import kotlin.time.Duration.Companion.seconds

import kotlinx.coroutines.*

suspend fun main() = coroutineScope {
    // Launches 50,000 coroutines that each wait five seconds, then print a period
    repeat(50_000) {
        launch {
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
Depending on your operating system, JDK version, and settings,
it may either throw an out-of-memory error or slow down thread creation to avoid running too many threads at once.

## What's next

* Discover more about combining suspending functions in [Composing suspending functions](composing-suspending-functions.md).
* Learn how to cancel coroutines and handle timeouts in [Cancellation and timeouts](cancellation-and-timeouts.md).
* Dive deeper into coroutine execution and thread management in [Coroutine context and dispatchers](coroutine-context-and-dispatchers.md).
* Learn how to return multiple asynchronously computed values in [Asynchronous flows](flow.md)
