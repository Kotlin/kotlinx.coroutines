<!--- INCLUDE .*/example-([a-z]+)-([0-9a-z]+)\.kt 
/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

// This file was automatically generated from coroutines-guide.md by Knit tool. Do not edit.
package kotlinx.coroutines.experimental.guide.$$1$$2

import kotlinx.coroutines.experimental.*
-->
<!--- KNIT     ../core/kotlinx-coroutines-core/test/guide/.*\.kt -->
<!--- TEST_OUT ../core/kotlinx-coroutines-core/test/guide/test/DispatcherGuideTest.kt
// This file was automatically generated from coroutines-guide.md by Knit tool. Do not edit.
package kotlinx.coroutines.experimental.guide.test

import org.junit.Test

class DispatchersGuideTest {
--> 

## Table of contents

<!--- TOC -->

* [Coroutine context and dispatchers](#coroutine-context-and-dispatchers)
  * [Dispatchers and threads](#dispatchers-and-threads)
  * [Unconfined vs confined dispatcher](#unconfined-vs-confined-dispatcher)
  * [Debugging coroutines and threads](#debugging-coroutines-and-threads)
  * [Jumping between threads](#jumping-between-threads)
  * [Job in the context](#job-in-the-context)
  * [Children of a coroutine](#children-of-a-coroutine)
  * [Parental responsibilities](#parental-responsibilities)
  * [Naming coroutines for debugging](#naming-coroutines-for-debugging)
  * [Combining context elements](#combining-context-elements)
  * [Cancellation via explicit job](#cancellation-via-explicit-job)
  * [Thread-local data](#thread-local-data)

<!--- END_TOC -->

## Coroutine context and dispatchers

Coroutines always execute in some context which is represented by the value of 
[CoroutineContext](https://kotlinlang.org/api/latest/jvm/stdlib/kotlin.coroutines.experimental/-coroutine-context/) 
type, defined in the Kotlin standard library.

The coroutine context is a set of various elements. The main elements are the [Job] of the coroutine, 
which we've seen before, and its dispatcher, which is covered in this section.

### Dispatchers and threads

Coroutine context includes a _coroutine dispatcher_ (see [CoroutineDispatcher]) that determines what thread or threads 
the corresponding coroutine uses for its execution. Coroutine dispatcher can confine coroutine execution 
to a specific thread, dispatch it to a thread pool, or let it run unconfined. 

All coroutine builders like [launch] and [async] accept an optional 
[CoroutineContext](https://kotlinlang.org/api/latest/jvm/stdlib/kotlin.coroutines.experimental/-coroutine-context/) 
parameter that can be used to explicitly specify the dispatcher for new coroutine and other context elements. 

Try the following example:

<!--- INCLUDE
import kotlin.coroutines.experimental.*
-->

<div class="sample" markdown="1" theme="idea" data-highlight-only>

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    launch { // context of the parent, main runBlocking coroutine
        println("main runBlocking      : I'm working in thread ${Thread.currentThread().name}")
    }
    launch(Dispatchers.Unconfined) { // not confined -- will work with main thread
        println("Unconfined            : I'm working in thread ${Thread.currentThread().name}")
    }
    launch(Dispatchers.Default) { // will get dispatched to DefaultDispatcher 
        println("Default               : I'm working in thread ${Thread.currentThread().name}")
    }
    launch(newSingleThreadContext("MyOwnThread")) { // will get its own new thread
        println("newSingleThreadContext: I'm working in thread ${Thread.currentThread().name}")
    }
}
```

</div>

> You can get full code [here](../core/kotlinx-coroutines-core/test/guide/example-context-01.kt)

It produces the following output (maybe in different order):

```text
Unconfined            : I'm working in thread main
Default               : I'm working in thread DefaultDispatcher-worker-1
newSingleThreadContext: I'm working in thread MyOwnThread
main runBlocking      : I'm working in thread main
```

<!--- TEST LINES_START_UNORDERED -->

When `launch { ... }` is used without parameters, it inherits the context (and thus dispatcher)
from the [CoroutineScope] that it is being launched from. In this case, it inherits the
context of the main `runBlocking` coroutine which runs in the `main` thread. 

[Dispatchers.Unconfined] is a special dispatcher that also appears to run in the `main` thread, but it is,
in fact, a different mechanism that is explained later.

The default dispatcher, that is used when coroutines are launched in [GlobalScope],
is represented by [Dispatchers.Default] and uses shared background pool of threads,
so `launch(Dispatchers.Default) { ... }` uses the same dispatcher as `GlobalScope.launch { ... }`.
  
[newSingleThreadContext] creates a new thread for the coroutine to run. 
A dedicated thread is a very expensive resource. 
In a real application it must be either released, when no longer needed, using [close][ExecutorCoroutineDispatcher.close] 
function, or stored in a top-level variable and reused throughout the application.  

### Unconfined vs confined dispatcher
 
The [Dispatchers.Unconfined] coroutine dispatcher starts coroutine in the caller thread, but only until the
first suspension point. After suspension it resumes in the thread that is fully determined by the
suspending function that was invoked. Unconfined dispatcher is appropriate when coroutine does not
consume CPU time nor updates any shared data (like UI) that is confined to a specific thread. 

On the other side, by default, a dispatcher for the outer [CoroutineScope] is inherited. 
The default dispatcher for [runBlocking] coroutine, in particular,
is confined to the invoker thread, so inheriting it has the effect of confining execution to
this thread with a predictable FIFO scheduling.

<!--- INCLUDE
import kotlin.coroutines.experimental.*
-->

<div class="sample" markdown="1" theme="idea" data-highlight-only>

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    launch(Dispatchers.Unconfined) { // not confined -- will work with main thread
        println("Unconfined      : I'm working in thread ${Thread.currentThread().name}")
        delay(500)
        println("Unconfined      : After delay in thread ${Thread.currentThread().name}")
    }
    launch { // context of the parent, main runBlocking coroutine
        println("main runBlocking: I'm working in thread ${Thread.currentThread().name}")
        delay(1000)
        println("main runBlocking: After delay in thread ${Thread.currentThread().name}")
    }
}
```

</div>

> You can get full code [here](../core/kotlinx-coroutines-core/test/guide/example-context-02.kt)

Produces the output: 
 
```text
Unconfined      : I'm working in thread main
main runBlocking: I'm working in thread main
Unconfined      : After delay in thread kotlinx.coroutines.DefaultExecutor
main runBlocking: After delay in thread main
```

<!--- TEST LINES_START -->
 
So, the coroutine that had inherited context of `runBlocking {...}` continues to execute
in the `main` thread, while the unconfined one had resumed in the default executor thread that [delay]
function is using.

> Unconfined dispatcher is an advanced mechanism that can be helpful in certain corner cases where
dispatching of coroutine for its execution later is not needed or produces undesirable side-effects,
because some operation in a coroutine must be performed right away. 
Unconfined dispatcher should not be used in general code.  

### Debugging coroutines and threads

Coroutines can suspend on one thread and resume on another thread. 
Even with a single-threaded dispatcher it might be hard to
figure out what coroutine was doing, where, and when. The common approach to debugging applications with 
threads is to print the thread name in the log file on each log statement. This feature is universally supported
by logging frameworks. When using coroutines, the thread name alone does not give much of a context, so 
`kotlinx.coroutines` includes debugging facilities to make it easier. 

Run the following code with `-Dkotlinx.coroutines.debug` JVM option:

<!--- INCLUDE
import kotlin.coroutines.experimental.*
-->

<div class="sample" markdown="1" theme="idea" data-highlight-only>

```kotlin
fun log(msg: String) = println("[${Thread.currentThread().name}] $msg")

fun main(args: Array<String>) = runBlocking<Unit> {
    val a = async {
        log("I'm computing a piece of the answer")
        6
    }
    val b = async {
        log("I'm computing another piece of the answer")
        7
    }
    log("The answer is ${a.await() * b.await()}")
}
```

</div>

> You can get full code [here](../core/kotlinx-coroutines-core/test/guide/example-context-03.kt)

There are three coroutines. The main coroutine (#1) -- `runBlocking` one, 
and two coroutines computing deferred values `a` (#2) and `b` (#3).
They are all executing in the context of `runBlocking` and are confined to the main thread.
The output of this code is:

```text
[main @coroutine#2] I'm computing a piece of the answer
[main @coroutine#3] I'm computing another piece of the answer
[main @coroutine#1] The answer is 42
```

<!--- TEST FLEXIBLE_THREAD -->

The `log` function prints the name of the thread in square brackets and you can see, that it is the `main`
thread, but the identifier of the currently executing coroutine is appended to it. This identifier 
is consecutively assigned to all created coroutines when debugging mode is turned on.

You can read more about debugging facilities in the documentation for [newCoroutineContext] function.

### Jumping between threads

Run the following code with `-Dkotlinx.coroutines.debug` JVM option (see [debug](#debugging-coroutines-and-threads)):

<div class="sample" markdown="1" theme="idea" data-highlight-only>

```kotlin
fun log(msg: String) = println("[${Thread.currentThread().name}] $msg")

fun main(args: Array<String>) {
    newSingleThreadContext("Ctx1").use { ctx1 ->
        newSingleThreadContext("Ctx2").use { ctx2 ->
            runBlocking(ctx1) {
                log("Started in ctx1")
                withContext(ctx2) {
                    log("Working in ctx2")
                }
                log("Back to ctx1")
            }
        }
    }
}
```

</div>

> You can get full code [here](../core/kotlinx-coroutines-core/test/guide/example-context-04.kt)

It demonstrates several new techniques. One is using [runBlocking] with an explicitly specified context, and
the other one is using [withContext] function to change a context of a coroutine while still staying in the
same coroutine as you can see in the output below:

```text
[Ctx1 @coroutine#1] Started in ctx1
[Ctx2 @coroutine#1] Working in ctx2
[Ctx1 @coroutine#1] Back to ctx1
```

<!--- TEST -->

Note, that this example also uses `use` function from the Kotlin standard library to release threads that
are created with [newSingleThreadContext] when they are no longer needed. 

### Job in the context

The coroutine's [Job] is part of its context. The coroutine can retrieve it from its own context 
using `coroutineContext[Job]` expression:

<!--- INCLUDE  
import kotlin.coroutines.experimental.*
-->

<div class="sample" markdown="1" theme="idea" data-highlight-only>

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    println("My job is ${coroutineContext[Job]}")
}
```

</div>

> You can get full code [here](../core/kotlinx-coroutines-core/test/guide/example-context-05.kt)

It produces something like that when running in [debug mode](#debugging-coroutines-and-threads):

```
My job is "coroutine#1":BlockingCoroutine{Active}@6d311334
```

<!--- TEST lines.size == 1 && lines[0].startsWith("My job is \"coroutine#1\":BlockingCoroutine{Active}@") -->

Note, that [isActive] in [CoroutineScope] is just a convenient shortcut for
`coroutineContext[Job]?.isActive == true`.

### Children of a coroutine

When a coroutine is launched in the [CoroutineScope] of another coroutine,
it inherits its context via [CoroutineScope.coroutineContext] and 
the [Job] of the new coroutine becomes
a _child_ of the parent coroutine's job. When the parent coroutine is cancelled, all its children
are recursively cancelled, too. 

However, when [GlobalScope] is used to launch a coroutine, it is not tied to the scope it
was launched from and operates independently.
  
<!--- INCLUDE
import kotlin.coroutines.experimental.*
-->

<div class="sample" markdown="1" theme="idea" data-highlight-only>

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    // launch a coroutine to process some kind of incoming request
    val request = launch {
        // it spawns two other jobs, one with GlobalScope
        GlobalScope.launch {
            println("job1: I run in GlobalScope and execute independently!")
            delay(1000)
            println("job1: I am not affected by cancellation of the request")
        }
        // and the other inherits the parent context
        launch {
            delay(100)
            println("job2: I am a child of the request coroutine")
            delay(1000)
            println("job2: I will not execute this line if my parent request is cancelled")
        }
    }
    delay(500)
    request.cancel() // cancel processing of the request
    delay(1000) // delay a second to see what happens
    println("main: Who has survived request cancellation?")
}
```

</div>

> You can get full code [here](../core/kotlinx-coroutines-core/test/guide/example-context-06.kt)

The output of this code is:

```text
job1: I run in GlobalScope and execute independently!
job2: I am a child of the request coroutine
job1: I am not affected by cancellation of the request
main: Who has survived request cancellation?
```

<!--- TEST -->

### Parental responsibilities 

A parent coroutine always waits for completion of all its children. Parent does not have to explicitly track
all the children it launches and it does not have to use [Job.join] to wait for them at the end:

<!--- INCLUDE
import kotlin.coroutines.experimental.*
-->

<div class="sample" markdown="1" theme="idea" data-highlight-only>

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    // launch a coroutine to process some kind of incoming request
    val request = launch {
        repeat(3) { i -> // launch a few children jobs
            launch  {
                delay((i + 1) * 200L) // variable delay 200ms, 400ms, 600ms
                println("Coroutine $i is done")
            }
        }
        println("request: I'm done and I don't explicitly join my children that are still active")
    }
    request.join() // wait for completion of the request, including all its children
    println("Now processing of the request is complete")
}
```

</div>

> You can get full code [here](../core/kotlinx-coroutines-core/test/guide/example-context-07.kt)

The result is going to be:

```text
request: I'm done and I don't explicitly join my children that are still active
Coroutine 0 is done
Coroutine 1 is done
Coroutine 2 is done
Now processing of the request is complete
```

<!--- TEST -->

### Naming coroutines for debugging

Automatically assigned ids are good when coroutines log often and you just need to correlate log records
coming from the same coroutine. However, when coroutine is tied to the processing of a specific request
or doing some specific background task, it is better to name it explicitly for debugging purposes.
[CoroutineName] context element serves the same function as a thread name. It'll get displayed in the thread name that
is executing this coroutine when [debugging mode](#debugging-coroutines-and-threads) is turned on.

The following example demonstrates this concept:

<div class="sample" markdown="1" theme="idea" data-highlight-only>

```kotlin
fun log(msg: String) = println("[${Thread.currentThread().name}] $msg")

fun main(args: Array<String>) = runBlocking(CoroutineName("main")) {
    log("Started main coroutine")
    // run two background value computations
    val v1 = async(CoroutineName("v1coroutine")) {
        delay(500)
        log("Computing v1")
        252
    }
    val v2 = async(CoroutineName("v2coroutine")) {
        delay(1000)
        log("Computing v2")
        6
    }
    log("The answer for v1 / v2 = ${v1.await() / v2.await()}")
}
```

</div>

> You can get full code [here](../core/kotlinx-coroutines-core/test/guide/example-context-08.kt)

The output it produces with `-Dkotlinx.coroutines.debug` JVM option is similar to:
 
```text
[main @main#1] Started main coroutine
[main @v1coroutine#2] Computing v1
[main @v2coroutine#3] Computing v2
[main @main#1] The answer for v1 / v2 = 42
```

<!--- TEST FLEXIBLE_THREAD -->

### Combining context elements

Sometimes we need to define multiple elements for coroutine context. We can use `+` operator for that.
For example, we can launch a coroutine with an explicitly specified dispatcher and an explicitly specified 
name at the same time: 

<!--- INCLUDE
import kotlin.coroutines.experimental.*
-->

<div class="sample" markdown="1" theme="idea" data-highlight-only>

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    launch(Dispatchers.Default + CoroutineName("test")) {
        println("I'm working in thread ${Thread.currentThread().name}")
    }
}
```

</div>

> You can get full code [here](../core/kotlinx-coroutines-core/test/guide/example-context-09.kt)

The output of this code  with `-Dkotlinx.coroutines.debug` JVM option is: 

```text
I'm working in thread DefaultDispatcher-worker-1 @test#2
```

<!--- TEST FLEXIBLE_THREAD -->

### Cancellation via explicit job

Let us put our knowledge about contexts, children and jobs together. Assume that our application has
an object with a lifecycle, but that object is not a coroutine. For example, we are writing an Android application
and launch various coroutines in the context of an Android activity to perform asynchronous operations to fetch 
and update data, do animations, etc. All of these coroutines must be cancelled when activity is destroyed
to avoid memory leaks. 
  
We manage a lifecycle of our coroutines by creating an instance of [Job] that is tied to 
the lifecycle of our activity. A job instance is created using [Job()] factory function when
activity is created and it is cancelled when an activity is destroyed like this:

<!--- INCLUDE
import kotlin.coroutines.experimental.*
-->

<div class="sample" markdown="1" theme="idea" data-highlight-only>

```kotlin
class Activity : CoroutineScope {
    lateinit var job: Job

    fun create() {
        job = Job()
    }

    fun destroy() {
        job.cancel()
    }
    // to be continued ...
```

</div>

We also implement [CoroutineScope] interface in this `Actvity` class. We only need to provide an override
for its [CoroutineScope.coroutineContext] property to specify the context for coroutines launched in its
scope. We combine the desired dispatcher (we used [Dispatchers.Default] in this example) and a job:

<div class="sample" markdown="1" theme="idea" data-highlight-only>

```kotlin
    // class Activity continues
    override val coroutineContext: CoroutineContext
        get() = Dispatchers.Default + job
    // to be continued ...
```

</div>

Now, we can launch coroutines in the scope of this `Activity` without having to explicitly
specify their context. For the demo, we launch ten coroutines that delay for a different time:

<div class="sample" markdown="1" theme="idea" data-highlight-only>

```kotlin
    // class Activity continues
    fun doSomething() {
        // launch ten coroutines for a demo, each working for a different time
        repeat(10) { i ->
            launch {
                delay((i + 1) * 200L) // variable delay 200ms, 400ms, ... etc
                println("Coroutine $i is done")
            }
        }
    }
} // class Activity ends
``` 

</div>

In our main function we create activity, call our test `doSomething` function, and destroy activity after 500ms.
This cancels all the coroutines that were launched which we can confirm by noting that it does not print 
onto the screen anymore if we wait: 

<div class="sample" markdown="1" theme="idea" data-highlight-only>

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    val activity = Activity()
    activity.create() // create an activity
    activity.doSomething() // run test function
    println("Launched coroutines")
    delay(500L) // delay for half a second
    println("Destroying activity!")
    activity.destroy() // cancels all coroutines
    delay(1000) // visually confirm that they don't work
}
```

</div>

> You can get full code [here](../core/kotlinx-coroutines-core/test/guide/example-context-10.kt)

The output of this example is:

```text
Launched coroutines
Coroutine 0 is done
Coroutine 1 is done
Destroying activity!
```

<!--- TEST -->

As you can see, only the first two coroutines had printed a message and the others were cancelled 
by a single invocation of `job.cancel()` in `Activity.destroy()`.

### Thread-local data

Sometimes it is convenient to have an ability to pass some thread-local data, but, for coroutines, which 
are not bound to any particular thread, it is hard to achieve it manually without writing a lot of boilerplate.

For [`ThreadLocal`](https://docs.oracle.com/javase/8/docs/api/java/lang/ThreadLocal.html), 
[asContextElement] extension function is here for the rescue. It creates an additional context element, 
which keeps the value of the given `ThreadLocal` and restores it every time the coroutine switches its context.

It is easy to demonstrate it in action:

<!--- INCLUDE
import kotlin.coroutines.experimental.*
-->

<div class="sample" markdown="1" theme="idea" data-highlight-only>

```kotlin
val threadLocal = ThreadLocal<String?>() // declare thread-local variable

fun main(args: Array<String>) = runBlocking<Unit> {
    threadLocal.set("main")
    println("Pre-main, current thread: ${Thread.currentThread()}, thread local value: '${threadLocal.get()}'")
    val job = launch(Dispatchers.Default + threadLocal.asContextElement(value = "launch")) {
       println("Launch start, current thread: ${Thread.currentThread()}, thread local value: '${threadLocal.get()}'")
        yield()
        println("After yield, current thread: ${Thread.currentThread()}, thread local value: '${threadLocal.get()}'")
    }
    job.join()
    println("Post-main, current thread: ${Thread.currentThread()}, thread local value: '${threadLocal.get()}'")
}
```  

</div>                                                                                       

> You can get full code [here](../core/kotlinx-coroutines-core/test/guide/example-context-11.kt)

In this example we launch new coroutine in a background thread pool using [Dispatchers.Default], so
it works on a different threads from a thread pool, but it still has the value of thread local variable,
that we've specified using `threadLocal.asContextElement(value = "launch")`,
no matter on what thread the coroutine is executed.
Thus, output (with [debug](#debugging-coroutines-and-threads)) is:

```text
Pre-main, current thread: Thread[main @coroutine#1,5,main], thread local value: 'main'
Launch start, current thread: Thread[DefaultDispatcher-worker-1 @coroutine#2,5,main], thread local value: 'launch'
After yield, current thread: Thread[DefaultDispatcher-worker-2 @coroutine#2,5,main], thread local value: 'launch'
Post-main, current thread: Thread[main @coroutine#1,5,main], thread local value: 'main'
```

<!--- TEST FLEXIBLE_THREAD -->

`ThreadLocal` has first-class support and can be used with any primitive `kotlinx.coroutines` provides.
It has one key limitation: when thread-local is mutated, a new value is not propagated to the coroutine caller 
(as context element cannot track all `ThreadLocal` object accesses) and updated value is lost on the next suspension.
Use [withContext] to update the value of the thread-local in a coroutine, see [asContextElement] for more details. 

Alternatively, a value can be stored in a mutable box like `class Counter(var i: Int)`, which is, in turn, 
is stored in a thread-local variable. However, in this case you are fully responsible to synchronize 
potentially concurrent modifications to the variable in this mutable box.

For advanced usage, for example for integration with logging MDC, transactional contexts or any other libraries
which internally use thread-locals for passing data, see documentation for [ThreadContextElement] interface 
that should be implemented. 

<!--- MODULE kotlinx-coroutines-core -->
<!--- INDEX kotlinx.coroutines.experimental -->
[Job]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-job/index.html
[CoroutineDispatcher]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-coroutine-dispatcher/index.html
[launch]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/launch.html
[async]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/async.html
[CoroutineScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-coroutine-scope/index.html
[Dispatchers.Unconfined]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-dispatchers/-unconfined.html
[GlobalScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-global-scope/index.html
[Dispatchers.Default]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-dispatchers/-default.html
[newSingleThreadContext]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/new-single-thread-context.html
[ExecutorCoroutineDispatcher.close]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-executor-coroutine-dispatcher/close.html
[runBlocking]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/run-blocking.html
[delay]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/delay.html
[newCoroutineContext]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/new-coroutine-context.html
[withContext]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/with-context.html
[isActive]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/is-active.html
[CoroutineScope.coroutineContext]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-coroutine-scope/coroutine-context.html
[Job.join]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-job/join.html
[CoroutineName]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-coroutine-name/index.html
[Job()]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-job.html
[asContextElement]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/java.lang.-thread-local/as-context-element.html
[ThreadContextElement]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-thread-context-element/index.html
<!--- END -->
