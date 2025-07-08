<!--- TEST_NAME BasicsGuideTest -->
<contribute-url>https://github.com/Kotlin/kotlinx.coroutines/edit/master/docs/topics/</contribute-url>

[//]: # (title: Coroutines basics)

To create applications that perform multiple tasks at once, a concept known as concurrency,
Kotlin uses coroutines. Coroutines let you write concurrent code in a clear and sequential style.

The most basic building block of coroutines is the suspending function.
It makes it possible to pause a running operation and resume it later without losing the structure of your code.

To mark a function as suspendable, use the `suspend` keyword:

```kotlin
suspend fun greet() {
    println("Hello world from a suspending function")
}
```

You can only call a suspending function from another suspending function or from a coroutine. 
Even the `main()` function can be suspending:

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

This example doesn’t use concurrency yet, but by marking the functions with the `suspend` keyword,
you allow them to be used in concurrent code later.

While the `suspend` keyword is part of the Kotlin standard library, most coroutine features
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

Suspending functions are the basic building blocks for concurrency in Kotlin, but they can only run inside another suspending function or a coroutine.
A coroutine is a suspendable computation that runs on _threads_ and can run concurrently or in parallel with other coroutines.

On the JVM, all concurrent code, such as coroutines, runs on threads, which are managed by the operating system.
Coroutines can suspend their execution instead of blocking a thread, which lets you run many tasks with less overhead.

> You can display coroutine names next to thread names in the output of your code for additional information.
> In IntelliJ IDEA, right-click the `Run` icon: ![Run icon](run-icon.png){width=30} next to your `main()` function, select `Modify Run Configuration...`, and add `-Dkotlinx.coroutines.debug` in `VM options`.
> 
> See [Debug coroutines using IntelliJ IDEA — Tutorial](debug-coroutines-with-idea.md) for more information.
> 
{style="tip"}  

To create a coroutine in Kotlin, you need a suspending function, a scope, a builder to start it, and a dispatcher to control which threads it uses:

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

    > While you can mark the `main()` function as `suspend` in some projects, other projects or frameworks might not allow changing the `main()` function this way.
    > In those cases, coroutine builder functions like [`runBlocking`](#runblocking) are the usual entry point for calling suspending code.
    > 
    {style="note"}


3. Use the [`coroutineScope()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/coroutine-scope.html) function to [create a `CoroutineScope`](#coroutine-scope-and-structured-concurrency) that groups your coroutines and controls their lifecycle:

    ```kotlin
    suspend fun main() = coroutineScope {
        // Add coroutine builder here
    }
    ```

4. Use a [coroutine builder function](#coroutine-builder-functions) like [`.launch()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/launch.html) to start the coroutine:

    ```kotlin
    suspend fun main() = coroutineScope {
        // Starts a coroutine inside the scope
        launch {
            greet()
        }
        println("This runs while the coroutine is active")
    }
    ```

5. Specify a [coroutine dispatcher](coroutine-context-and-dispatchers.md) like [`Dispatchers.Default`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-dispatchers/-default.html) to control the [thread pool](#comparing-coroutines-and-jvm-threads) for your coroutine:

    ```kotlin
    suspend fun main() = coroutineScope {
        // Starts a coroutine inside the scope with a specified dispatcher
        launch(Dispatchers.Default) {
            greet()
        }
        println("This runs while the coroutine is active")
    }
    ```

   > If you don’t specify a coroutine dispatcher, a coroutine builder like `.launch()` inherits the dispatcher from its `CoroutineScope`.
   > If the scope doesn’t define a dispatcher, the builder uses `Dispatchers.Default`.
   >
   {style="note"}

6. Combine these pieces to run multiple coroutines at the same time on a shared pool of threads:

    ```kotlin
    // Imports the coroutines library
    import kotlinx.coroutines.*
    
    // Defines a suspending function
    suspend fun greet() {
    println("Hello from greet() on thread: ${Thread.currentThread().name}")
    }
    
    suspend fun main() = coroutineScope {
    // Starts a coroutine with Dispatchers.Default
    launch(Dispatchers.Default) {
        greet()
    }
   
        // Starts another coroutine
        launch(Dispatchers.Default) {
            println("Second coroutine on thread: ${Thread.currentThread().name}")
        }
    
        // Runs code in the coroutine scope
        println("This runs while the coroutine is active")
    }
    ```
    {kotlin-runnable="true"}

This example demonstrates simple multithreading with coroutines on a shared thread pool.

> Try running the example multiple times. 
> You may notice that the output order and thread names may change each time you run the program. 
> This is because the JVM and OS decide when threads run and tasks complete.
> 
{style="tip"}

## Coroutine scope and structured concurrency

Coroutines follow a principle of _structured concurrency_, which means new coroutines can only be launched in a specific [`CoroutineScope`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-coroutine-scope/) that defines their lifecycle.

When you work with multiple coroutines, you often need to run many tasks at once, cancel them when they are no longer needed, and handle errors safely.
Without clear structure, you risk leaving coroutines running longer than needed, wasting resources.

Structured concurrency keeps coroutines organized in a hierarchy.
When you launch a coroutine, it belongs to its scope.
If the scope is canceled, all its child coroutines are canceled too.

[Coroutine builder functions](#coroutine-builder-functions) are extension functions on `CoroutineScope`.
When you start a coroutine inside another coroutine, it automatically becomes a child of its parent scope.
The parent coroutine's scope waits for all its children to finish before it completes.

To create a coroutine scope without launching a new coroutine, use the [`coroutineScope()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/coroutine-scope.html) function:

```kotlin
import kotlinx.coroutines.*

suspend fun main() = coroutineScope {
    // Starts a new coroutine in the coroutine scope
    launch {
        // Suspends for one second without blocking the thread
        delay(1000L)
        println("Child coroutine completed")
    }
    launch {
        delay(2000L)
        println("Another child coroutine completed")
    }

    // Runs immediately in the parent coroutine
    println("Coroutine scope completed")
}
```
{kotlin-runnable="true"}

This example uses the [`delay()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/delay.html#) function to show how the coroutine scope waits for its child coroutines to finish.
You can specify the wait time in milliseconds, so `delay(1000L)` suspends the coroutine for one second without blocking the thread.

## Coroutine builder functions

Coroutine builder functions create new coroutines inside an existing [coroutine scope](#coroutine-scope-and-structured-concurrency).
Each builder defines how the coroutine starts and how you interact with its result.

### .launch()

The [`.launch()`()](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/launch.html#) coroutine builder function starts a new coroutine without blocking the rest of the scope.
Use `.launch()` to run a task alongside other work when the result isn't needed or you don't want to wait for it:

```kotlin
import kotlinx.coroutines.*

suspend fun main() = coroutineScope {
    // Starts a coroutine that runs without blocking the scope
    launch {
        println("Sending notification in background")
    }

    // Main coroutine continues while a previous one is delayed
    println("Scope continues")
}
```
{kotlin-runnable="true"}

After running this example, you can see that the `main()` function isn’t blocked by `.launch()` and keeps running other code while the coroutine works in the background.

### .async()

Use the [`.async()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/async.html) builder function to start an asynchronous computation that runs alongside other code and returns a result you can access later.
The result is wrapped in a `Deferred` object, which you can access by calling the `.await()` function:

```kotlin
import kotlinx.coroutines.*

suspend fun main() = coroutineScope {
    // Starts a coroutine that returns a number
    val result = async {
        2 + 3
    }

    // Gets the result from the coroutine with the await() function
    println("The result is ${result.await()}")
}
```
{kotlin-runnable="true"}

### .runBlocking()

Use the [`.runBlocking()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/run-blocking.html) coroutine builder function to create a coroutine scope in a blocking context.
Instead of using a shared thread pool, `.runBlocking()` blocks the [thread](#comparing-coroutines-and-jvm-threads) it runs on and waits for all coroutines inside it to finish before continuing.

`.runBlocking()` creates a new `CoroutineScope` for the code inside it.
This lets you call suspending functions without marking the surrounding function as `suspend`, for example, in the `main()` function:

```kotlin
import kotlinx.coroutines.*

// Runs the greet() function inside a blocking scope
fun main() = runBlocking {
    greet()
    delay(1000L)
    println("Done")
}

suspend fun greet() {
    println("Hello from a suspending function")
}
```
{kotlin-runnable="true"}

<!--- 
## An explicit job

A [launch] coroutine builder returns a [Job] object that is a handle to the launched coroutine and can be 
used to wait for its completion explicitly.
For example, you can wait for the completion of the child coroutine and then print the "Done" string:

```kotlin
import kotlinx.coroutines.*

fun main() = runBlocking {
//sampleStart
    val job = launch { // launch a new coroutine and keep a reference to its Job
        delay(1000L)
        println("World!")
    }
    println("Hello")
    job.join() // wait until child coroutine completes
    println("Done") 
//sampleEnd    
}
```
{kotlin-runnable="true" kotlin-min-compiler-version="1.3"}
-->

## Coroutine dispatchers

A [coroutine dispatcher](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-dispatchers/#) controls which thread or thread pool coroutines use for their execution.
Coroutines are not tied to a single thread.
They can pause on one thread and resume on another, depending on the dispatcher.
This lets you run many coroutines at the same time without blocking threads.

A dispatcher works together with the [coroutine scope](#coroutine-scope-and-structured-concurrency) to define when coroutines run and where they run.
While the coroutine scope controls the coroutine’s lifecycle, the dispatcher controls which threads are used for execution.

> You don't have to create a dispatcher for every coroutine.
> By default, coroutines inherit the dispatcher from their parent scope.
> You can specify a dispatcher if you need to run a coroutine in a different context.
>
{style="note"}

The `kotlinx.coroutines` library includes different dispatchers for different use cases.
For example, [`Dispatchers.Default`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-dispatchers/-default.html) runs coroutines on a shared pool of threads performing work in the background,
separate from the main thread.
This multithreaded dispatcher is optimized for CPU-intensive tasks like calculations or data processing:

```kotlin
import kotlinx.coroutines.*

fun main() = runBlocking {
    // Runs runBlocking on the main thread
    println("runBlocking running on ${Thread.currentThread().name}")

    val one = async(Dispatchers.Default) {
        // Starts first calculation on a thread in the Default dispatcher’s thread pool
        println("First calculation starting on ${Thread.currentThread().name}")
        val sum = (1..500_000).sum()
        // Suspends for 200 ms
        delay(200L)
        println("First calculation done on ${Thread.currentThread().name}")
        sum
    }

    val two = async(Dispatchers.Default) {
        // Starts second calculation on a thread in the Default dispatcher’s thread pool
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

Let’s look at an example where 50,000 coroutines each wait five seconds and then print a period (`.`):

```kotlin
import kotlinx.coroutines.*

fun main() = runBlocking {
    repeat(50_000) { // launch a lot of coroutines
        launch {
            delay(5000L)
            print(".")
        }
    }
}
```
{kotlin-runnable="true" kotlin-min-compiler-version="1.3"}
<!--- KNIT example-basic-06.kt -->
<!--- > You can get the full code [here](https://github.com/Kotlin/kotlinx.coroutines/blob/master/kotlinx-coroutines-core/jvm/test/guide/example-basic-06.kt).
>
{style="note"}
-->

<!--- TEST lines.size == 1 && lines[0] == ".".repeat(50_000) -->

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

<!--- MODULE kotlinx-coroutines-core -->
<!--- INDEX kotlinx.coroutines -->

## What's next

* Discover more about combining suspending functions in [Composing suspending functions](composing-suspending-functions.md).
* Learn how to cancel coroutines and handle timeouts in [Cancellation and timeouts](cancellation-and-timeouts.md).
* Dive deeper into coroutine execution and thread management in [Coroutine context and dispatchers](coroutine-context-and-dispatchers.md).
* Learn how to return multiple asynchronously computed values in [Asynchronous flows](flow.md)

<!--- END -->
