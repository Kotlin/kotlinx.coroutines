[//]: # (title: Create a basic coroutine – tutorial)

Kotlin 1.1 introduced coroutines, a new way of writing asynchronous, non-blocking code (and much more). In this tutorial you will go through some basics of using Kotlin coroutines with the help of the `kotlinx.coroutines` library, which is a collection of helpers and wrappers for existing Java libraries.

## Set up a project

### Gradle

In IntelliJ IDEA go to **File** \| **New** \| **Project**.:

![Create a new project](new-gradle-project-jvm.png)

Then follow the wizard steps. You'll have a `build.gradle` file created with Kotlin configured according to [this document](gradle.md).
Make sure it's configured for Kotlin 1.3 or higher.

Since we'll be using the [`kotlinx.coroutines`](https://github.com/Kotlin/kotlinx.coroutines), let's add its recent version to our dependencies:

<tabs>

```groovy
dependencies {
    ...
    implementation 'org.jetbrains.kotlinx:kotlinx-coroutines-core:%coroutinesVersion%'
}
```

```kotlin
dependencies {
    ...
    implementation("org.jetbrains.kotlinx:kotlinx-coroutines-core:%coroutinesVersion%")
}
```
</tabs>

This library is published to Maven Central repository, so add the following:

```groovy
repositories {
    mavenCentral()
}
```

That's it, we are good to go and write code under `src/main/kotlin`.

### Maven

In IntelliJ IDEA go to **File** \| **New** \| **Project** and check the **Create from archetype** box:

![Create a new project](new-mvn-project-jvm.png)

Then follow the wizard steps. You'll have a `pom.xml`  file created with Kotlin configured according to [this document](maven.md).
Make sure it's configured for Kotlin 1.3 or higher.

```xml
<plugin>
    <groupId>org.jetbrains.kotlin</groupId>
    <artifactId>kotlin-maven-plugin</artifactId>
    ...
    <configuration>
        <args>
            <arg>-Xcoroutines=enable</arg>
        </args>
    </configuration>
</plugin>
```

Since we'll be using the [`kotlinx.coroutines`](https://github.com/Kotlin/kotlinx.coroutines), let's add its recent version to our dependencies:

```xml
<dependencies>
    ...
    <dependency>
        <groupId>org.jetbrains.kotlinx</groupId>
        <artifactId>kotlinx-coroutines-core</artifactId>
        <version>%coroutinesVersion%</version>
    </dependency>
</dependencies>
```

That's it, we are good to go and write code under `src/main/kotlin`.

## My first coroutine

One can think of a coroutine as a light-weight thread. Like threads, coroutines can run in parallel, wait for each other and communicate.
The biggest difference is that coroutines are very cheap, almost free: we can create thousands of them, and pay very little in terms of performance.
True threads, on the other hand, are expensive to start and keep around. A thousand threads can be a serious challenge for a modern machine.

So, how do we start a coroutine? Let's use the `launch {}` function:

```kotlin
launch {
    ...
}
```

This starts a new coroutine. By default, coroutines are run on a shared pool of threads. 
Threads still exist in a program based on coroutines, but one thread can run many coroutines, so there's no need for 
too many threads.

Let's look at a full program that uses `launch`:

```kotlin
import kotlinx.coroutines.*

fun main(args: Array<String>) {
//sampleStart
    println("Start")

    // Start a coroutine
    GlobalScope.launch {
        delay(1000)
        println("Hello")
    }

    Thread.sleep(2000) // wait for 2 seconds
    println("Stop")
//sampleEnd
}
```
{kotlin-runnable="true" kotlin-min-compiler-version="1.3"}

Here we start a coroutine that waits for 1 second and prints `Hello`.

We are using the `delay()` function that's like `Thread.sleep()`, but better: it _doesn't block a thread_, but only suspends the coroutine itself.
The thread is returned to the pool while the coroutine is waiting, and when the waiting is done, the coroutine resumes on a free thread in the pool.

The main thread (that runs the `main()` function) must wait until our coroutine completes, otherwise the program ends before `Hello` is printed.

_Exercise: try removing the `sleep()` from the program above and see the result._

 If we try to use the same non-blocking `delay()` function directly inside `main()`, we'll get a compiler error:

> Suspend functions are only allowed to be called from a coroutine or another suspend function.
>
{type="note"}

This is because we are not inside any coroutine. We can use delay if we wrap it into `runBlocking {}` that starts a coroutine and waits until it's done:

```kotlin
runBlocking {
    delay(2000)
}
```

So, first the resulting program prints `Start`, then it runs a coroutine through `launch {}`, then it runs another one through `runBlocking {}` and blocks until it's done, then prints `Stop`. Meanwhile the first coroutine completes and prints `Hello`. Just like threads, we told you :)

## Let's run a lot of them

Now, let's make sure that coroutines are really cheaper than threads. How about starting a million of them? Let's try starting a million threads first:

```kotlin
val c = AtomicLong()

for (i in 1..1_000_000L)
    thread(start = true) {
        c.addAndGet(i)
    }

println(c.get())
```

This runs a 1'000'000 threads each of which adds to a common counter. My patience runs out before this program completes on my machine (definitely over a minute).

Let's try the same with coroutines:

```kotlin
val c = AtomicLong()

for (i in 1..1_000_000L)
    GlobalScope.launch {
        c.addAndGet(i)
    }

println(c.get())
```

This example completes in less than a second for me, but it prints some arbitrary number, because some coroutines don't finish before `main()` prints the result. Let's fix that.

We could use the same means of synchronization that are applicable to threads (a `CountDownLatch` is what crosses my mind in this case), but let's take a safer and cleaner path.

## Async: returning a value from a coroutine

Another way of starting a coroutine is `async {}`. It is like `launch {}`, but returns an instance of `Deferred<T>`, which has an `await()` function that returns the result of the coroutine. `Deferred<T>` is a very basic [future](https://en.wikipedia.org/wiki/Futures_and_promises) (fully-fledged JDK futures are also supported, but here we'll confine ourselves to `Deferred` for now).

Let's create a million coroutines again, keeping their `Deferred` objects. Now there's no need in the atomic counter, as we can just return the numbers to be added from our coroutines:

```kotlin
val deferred = (1..1_000_000).map { n ->
    GlobalScope.async {
        n
    }
}
```

All these have already started, all we need is collect the results:

```kotlin
val sum = deferred.sumOf { it.await().toLong() }
```

We simply take every coroutine and await its result here, then all results are added together by the standard library function `sumOf()`. But the compiler rightfully complains:

> Suspend functions are only allowed to be called from a coroutine or another suspend function.
>
{type="note"}

`await()` can not be called outside a coroutine, because it needs to suspend until the computation finishes, and only coroutines can suspend in a non-blocking way. So, let's put this inside a coroutine:

```kotlin
runBlocking {
    val sum = deferred.sumOf { it.await().toLong() }
    println("Sum: $sum")
}
```

Now it prints something sensible: `500000500000`, because all coroutines complete.

Let's also make sure that our coroutines actually run in parallel. If we add a 1-second `delay()` to each of the `async`'s, the resulting program won't run for 1'000'000 seconds (over 11,5 days):

```kotlin
val deferred = (1..1_000_000).map { n ->
    GlobalScope.async {
        delay(1000)
        n
    }
}
```

This takes about 10 seconds on my machine, so yes, coroutines do run in parallel.

## Suspending functions

Now, let's say we want to extract our _workload_ (which is "wait 1 second and return a number") into a separate function:

```kotlin
fun workload(n: Int): Int {
    delay(1000)
    return n
}
```

A familiar error pops up:

> Suspend functions are only allowed to be called from a coroutine or another suspend function.
>
{type="note"}

Let's dig a little into what it means. The biggest merit of coroutines is that they can _suspend_ without blocking a thread. The compiler has to emit some special code to make this possible, so we have to mark functions that _may suspend_ explicitly in the code. We use the `suspend` modifier for it:

```kotlin
suspend fun workload(n: Int): Int {
    delay(1000)
    return n
}
```

Now when we call `workload()` from a coroutine, the compiler knows that it may suspend and will prepare accordingly:

```kotlin
GlobalScope.async {
    workload(n)
}
```

Our `workload()` function can be called from a coroutine (or another suspending function), but _cannot_ be called from outside a coroutine. Naturally, `delay()` and `await()` that we used above are themselves declared as `suspend`, and this is why we had to put them inside `runBlocking {}`, `launch {}` or `async {}`.
