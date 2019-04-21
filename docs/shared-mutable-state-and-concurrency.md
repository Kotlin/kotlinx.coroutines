<!--- INCLUDE .*/example-([a-z]+)-([0-9a-z]+)\.kt 
/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

// This file was automatically generated from coroutines-guide.md by Knit tool. Do not edit.
package kotlinx.coroutines.guide.$$1$$2
-->
<!--- KNIT     ../kotlinx-coroutines-core/jvm/test/guide/.*\.kt -->
<!--- TEST_OUT ../kotlinx-coroutines-core/jvm/test/guide/test/SharedStateGuideTest.kt
// This file was automatically generated from coroutines-guide.md by Knit tool. Do not edit.
package kotlinx.coroutines.guide.test

import org.junit.Test

class SharedStateGuideTest {
--> 
**Table of contents**

<!--- TOC -->

* [Shared mutable state and concurrency](#shared-mutable-state-and-concurrency)
  * [The problem](#the-problem)
  * [Volatiles are of no help](#volatiles-are-of-no-help)
  * [Thread-safe data structures](#thread-safe-data-structures)
  * [Thread confinement fine-grained](#thread-confinement-fine-grained)
  * [Thread confinement coarse-grained](#thread-confinement-coarse-grained)
  * [Mutual exclusion](#mutual-exclusion)
  * [Actors](#actors)

<!--- END_TOC -->

## Shared mutable state and concurrency

Coroutines can be executed concurrently using a multi-threaded dispatcher like the [Dispatchers.Default]. It presents
all the usual concurrency problems. The main problem being synchronization of access to **shared mutable state**. 
Some solutions to this problem in the land of coroutines are similar to the solutions in the multi-threaded world, 
but others are unique.

### The problem

Let us launch a hundred coroutines all doing the same action thousand times. 
We'll also measure their completion time for further comparisons:

<div class="sample" markdown="1" theme="idea" data-highlight-only>

```kotlin
suspend fun CoroutineScope.massiveRun(action: suspend () -> Unit) {
    val n = 100  // number of coroutines to launch
    val k = 1000 // times an action is repeated by each coroutine
    val time = measureTimeMillis {
        val jobs = List(n) {
            launch {
                repeat(k) { action() }
            }
        }
        jobs.forEach { it.join() }
    }
    println("Completed ${n * k} actions in $time ms")    
}
```

</div> 

We start with a very simple action that increments a shared mutable variable using 
multi-threaded [Dispatchers.Default] that is used in [GlobalScope]. 

<!--- CLEAR -->

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

```kotlin
import kotlinx.coroutines.*
import kotlin.system.*    

suspend fun CoroutineScope.massiveRun(action: suspend () -> Unit) {
    val n = 100  // number of coroutines to launch
    val k = 1000 // times an action is repeated by each coroutine
    val time = measureTimeMillis {
        val jobs = List(n) {
            launch {
                repeat(k) { action() }
            }
        }
        jobs.forEach { it.join() }
    }
    println("Completed ${n * k} actions in $time ms")    
}

var counter = 0

fun main() = runBlocking<Unit> {
//sampleStart
    GlobalScope.massiveRun {
        counter++
    }
    println("Counter = $counter")
//sampleEnd    
}
```

</div>

> You can get full code [here](../kotlinx-coroutines-core/jvm/test/guide/example-sync-01.kt).

<!--- TEST LINES_START
Completed 100000 actions in
Counter =
-->

What does it print at the end? It is highly unlikely to ever print "Counter = 100000", because a thousand coroutines 
increment the `counter` concurrently from multiple threads without any synchronization.

> Note: if you have an old system with 2 or fewer CPUs, then you _will_ consistently see 100000, because
the thread pool is running in only one thread in this case. To reproduce the problem you'll need to make the
following change:

<!--- CLEAR -->

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

```kotlin
import kotlinx.coroutines.*
import kotlin.system.*

suspend fun CoroutineScope.massiveRun(action: suspend () -> Unit) {
    val n = 100  // number of coroutines to launch
    val k = 1000 // times an action is repeated by each coroutine
    val time = measureTimeMillis {
        val jobs = List(n) {
            launch {
                repeat(k) { action() }
            }
        }
        jobs.forEach { it.join() }
    }
    println("Completed ${n * k} actions in $time ms")    
}

val mtContext = newFixedThreadPoolContext(2, "mtPool") // explicitly define context with two threads
var counter = 0

fun main() = runBlocking<Unit> {
//sampleStart
    CoroutineScope(mtContext).massiveRun { // use it instead of Dispatchers.Default in this sample and below 
        counter++
    }
    println("Counter = $counter")
//sampleEnd    
}
```

</div>

> You can get full code [here](../kotlinx-coroutines-core/jvm/test/guide/example-sync-01b.kt).

<!--- TEST LINES_START
Completed 100000 actions in
Counter =
-->

### Volatiles are of no help

There is common misconception that making a variable `volatile` solves concurrency problem. Let us try it:

<!--- CLEAR -->

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

```kotlin
import kotlinx.coroutines.*
import kotlin.system.*

suspend fun CoroutineScope.massiveRun(action: suspend () -> Unit) {
    val n = 100  // number of coroutines to launch
    val k = 1000 // times an action is repeated by each coroutine
    val time = measureTimeMillis {
        val jobs = List(n) {
            launch {
                repeat(k) { action() }
            }
        }
        jobs.forEach { it.join() }
    }
    println("Completed ${n * k} actions in $time ms")    
}

@Volatile // in Kotlin `volatile` is an annotation 
var counter = 0

fun main() = runBlocking<Unit> {
    GlobalScope.massiveRun {
        counter++
    }
    println("Counter = $counter")
}
```

</div>

> You can get full code [here](../kotlinx-coroutines-core/jvm/test/guide/example-sync-02.kt).

<!--- TEST LINES_START
Completed 100000 actions in
Counter =
-->

This code works slower, but we still don't get "Counter = 100000" at the end, because volatile variables guarantee
linearizable (this is a technical term for "atomic") reads and writes to the corresponding variable, but
do not provide atomicity of larger actions (increment in our case).

### Thread-safe data structures

The general solution that works both for threads and for coroutines is to use a thread-safe (aka synchronized,
linearizable, or atomic) data structure that provides all the necessarily synchronization for the corresponding 
operations that needs to be performed on a shared state. 
In the case of a simple counter we can use `AtomicInteger` class which has atomic `incrementAndGet` operations:

<!--- CLEAR -->

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

```kotlin
import kotlinx.coroutines.*
import java.util.concurrent.atomic.*
import kotlin.system.*

suspend fun CoroutineScope.massiveRun(action: suspend () -> Unit) {
    val n = 100  // number of coroutines to launch
    val k = 1000 // times an action is repeated by each coroutine
    val time = measureTimeMillis {
        val jobs = List(n) {
            launch {
                repeat(k) { action() }
            }
        }
        jobs.forEach { it.join() }
    }
    println("Completed ${n * k} actions in $time ms")    
}

var counter = AtomicInteger()

fun main() = runBlocking<Unit> {
//sampleStart
    GlobalScope.massiveRun {
        counter.incrementAndGet()
    }
    println("Counter = ${counter.get()}")
//sampleEnd    
}
```

</div>

> You can get full code [here](../kotlinx-coroutines-core/jvm/test/guide/example-sync-03.kt).

<!--- TEST ARBITRARY_TIME
Completed 100000 actions in xxx ms
Counter = 100000
-->

This is the fastest solution for this particular problem. It works for plain counters, collections, queues and other
standard data structures and basic operations on them. However, it does not easily scale to complex
state or to complex operations that do not have ready-to-use thread-safe implementations. 

### Thread confinement fine-grained

_Thread confinement_ is an approach to the problem of shared mutable state where all access to the particular shared
state is confined to a single thread. It is typically used in UI applications, where all UI state is confined to 
the single event-dispatch/application thread. It is easy to apply with coroutines by using a  
single-threaded context. 

<!--- CLEAR -->

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

```kotlin
import kotlinx.coroutines.*
import kotlin.system.*

suspend fun CoroutineScope.massiveRun(action: suspend () -> Unit) {
    val n = 100  // number of coroutines to launch
    val k = 1000 // times an action is repeated by each coroutine
    val time = measureTimeMillis {
        val jobs = List(n) {
            launch {
                repeat(k) { action() }
            }
        }
        jobs.forEach { it.join() }
    }
    println("Completed ${n * k} actions in $time ms")    
}

val counterContext = newSingleThreadContext("CounterContext")
var counter = 0

fun main() = runBlocking<Unit> {
//sampleStart
    GlobalScope.massiveRun { // run each coroutine with DefaultDispathcer
        withContext(counterContext) { // but confine each increment to the single-threaded context
            counter++
        }
    }
    println("Counter = $counter")
//sampleEnd    
}
```

</div>

> You can get full code [here](../kotlinx-coroutines-core/jvm/test/guide/example-sync-04.kt).

<!--- TEST ARBITRARY_TIME
Completed 100000 actions in xxx ms
Counter = 100000
-->

This code works very slowly, because it does _fine-grained_ thread-confinement. Each individual increment switches 
from multi-threaded [Dispatchers.Default] context to the single-threaded context using [withContext] block.

### Thread confinement coarse-grained

In practice, thread confinement is performed in large chunks, e.g. big pieces of state-updating business logic
are confined to the single thread. The following example does it like that, running each coroutine in 
the single-threaded context to start with. 
Here we use [CoroutineScope()] function to convert coroutine context reference to [CoroutineScope]:

<!--- CLEAR -->

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

```kotlin
import kotlinx.coroutines.*
import kotlin.system.*

suspend fun CoroutineScope.massiveRun(action: suspend () -> Unit) {
    val n = 100  // number of coroutines to launch
    val k = 1000 // times an action is repeated by each coroutine
    val time = measureTimeMillis {
        val jobs = List(n) {
            launch {
                repeat(k) { action() }
            }
        }
        jobs.forEach { it.join() }
    }
    println("Completed ${n * k} actions in $time ms")    
}

val counterContext = newSingleThreadContext("CounterContext")
var counter = 0

fun main() = runBlocking<Unit> {
//sampleStart
    CoroutineScope(counterContext).massiveRun { // run each coroutine in the single-threaded context
        counter++
    }
    println("Counter = $counter")
//sampleEnd    
}
```

</div>

> You can get full code [here](../kotlinx-coroutines-core/jvm/test/guide/example-sync-05.kt).

<!--- TEST ARBITRARY_TIME
Completed 100000 actions in xxx ms
Counter = 100000
-->

This now works much faster and produces correct result.

### Mutual exclusion

Mutual exclusion solution to the problem is to protect all modifications of the shared state with a _critical section_
that is never executed concurrently. In a blocking world you'd typically use `synchronized` or `ReentrantLock` for that.
Coroutine's alternative is called [Mutex]. It has [lock][Mutex.lock] and [unlock][Mutex.unlock] functions to 
delimit a critical section. The key difference is that `Mutex.lock()` is a suspending function. It does not block a thread.

There is also [withLock] extension function that conveniently represents 
`mutex.lock(); try { ... } finally { mutex.unlock() }` pattern: 

<!--- CLEAR -->

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.sync.*
import kotlin.system.*

suspend fun CoroutineScope.massiveRun(action: suspend () -> Unit) {
    val n = 100  // number of coroutines to launch
    val k = 1000 // times an action is repeated by each coroutine
    val time = measureTimeMillis {
        val jobs = List(n) {
            launch {
                repeat(k) { action() }
            }
        }
        jobs.forEach { it.join() }
    }
    println("Completed ${n * k} actions in $time ms")    
}

val mutex = Mutex()
var counter = 0

fun main() = runBlocking<Unit> {
//sampleStart
    GlobalScope.massiveRun {
        mutex.withLock {
            counter++        
        }
    }
    println("Counter = $counter")
//sampleEnd    
}
```

</div>

> You can get full code [here](../kotlinx-coroutines-core/jvm/test/guide/example-sync-06.kt).

<!--- TEST ARBITRARY_TIME
Completed 100000 actions in xxx ms
Counter = 100000
-->

The locking in this example is fine-grained, so it pays the price. However, it is a good choice for some situations
where you absolutely must modify some shared state periodically, but there is no natural thread that this state
is confined to.

### Actors

An [actor](https://en.wikipedia.org/wiki/Actor_model) is an entity made up of a combination of a coroutine, the state that is confined and encapsulated into this coroutine,
and a channel to communicate with other coroutines. A simple actor can be written as a function, 
but an actor with a complex state is better suited for a class. 

There is an [actor] coroutine builder that conveniently combines actor's mailbox channel into its 
scope to receive messages from and combines the send channel into the resulting job object, so that a 
single reference to the actor can be carried around as its handle.

The first step of using an actor is to define a class of messages that an actor is going to process.
Kotlin's [sealed classes](https://kotlinlang.org/docs/reference/sealed-classes.html) are well suited for that purpose.
We define `CounterMsg` sealed class with `IncCounter` message to increment a counter and `GetCounter` message
to get its value. The later needs to send a response. A [CompletableDeferred] communication
primitive, that represents a single value that will be known (communicated) in the future,
is used here for that purpose.

<div class="sample" markdown="1" theme="idea" data-highlight-only>

```kotlin
// Message types for counterActor
sealed class CounterMsg
object IncCounter : CounterMsg() // one-way message to increment counter
class GetCounter(val response: CompletableDeferred<Int>) : CounterMsg() // a request with reply
```

</div>

Then we define a function that launches an actor using an [actor] coroutine builder:

<div class="sample" markdown="1" theme="idea" data-highlight-only>

```kotlin
// This function launches a new counter actor
fun CoroutineScope.counterActor() = actor<CounterMsg> {
    var counter = 0 // actor state
    for (msg in channel) { // iterate over incoming messages
        when (msg) {
            is IncCounter -> counter++
            is GetCounter -> msg.response.complete(counter)
        }
    }
}
```

</div>

The main code is straightforward:

<!--- CLEAR -->

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlin.system.*

suspend fun CoroutineScope.massiveRun(action: suspend () -> Unit) {
    val n = 100  // number of coroutines to launch
    val k = 1000 // times an action is repeated by each coroutine
    val time = measureTimeMillis {
        val jobs = List(n) {
            launch {
                repeat(k) { action() }
            }
        }
        jobs.forEach { it.join() }
    }
    println("Completed ${n * k} actions in $time ms")    
}

// Message types for counterActor
sealed class CounterMsg
object IncCounter : CounterMsg() // one-way message to increment counter
class GetCounter(val response: CompletableDeferred<Int>) : CounterMsg() // a request with reply

// This function launches a new counter actor
fun CoroutineScope.counterActor() = actor<CounterMsg> {
    var counter = 0 // actor state
    for (msg in channel) { // iterate over incoming messages
        when (msg) {
            is IncCounter -> counter++
            is GetCounter -> msg.response.complete(counter)
        }
    }
}

fun main() = runBlocking<Unit> {
//sampleStart
    val counter = counterActor() // create the actor
    GlobalScope.massiveRun {
        counter.send(IncCounter)
    }
    // send a message to get a counter value from an actor
    val response = CompletableDeferred<Int>()
    counter.send(GetCounter(response))
    println("Counter = ${response.await()}")
    counter.close() // shutdown the actor
//sampleEnd    
}
```

</div>

> You can get full code [here](../kotlinx-coroutines-core/jvm/test/guide/example-sync-07.kt).

<!--- TEST ARBITRARY_TIME
Completed 100000 actions in xxx ms
Counter = 100000
-->

It does not matter (for correctness) what context the actor itself is executed in. An actor is
a coroutine and a coroutine is executed sequentially, so confinement of the state to the specific coroutine
works as a solution to the problem of shared mutable state. Indeed, actors may modify their own private state, but can only affect each other through messages (avoiding the need for any locks).

Actor is more efficient than locking under load, because in this case it always has work to do and it does not 
have to switch to a different context at all.

> Note that an [actor] coroutine builder is a dual of [produce] coroutine builder. An actor is associated 
  with the channel that it receives messages from, while a producer is associated with the channel that it 
  sends elements to.

<!--- MODULE kotlinx-coroutines-core -->
<!--- INDEX kotlinx.coroutines -->
[Dispatchers.Default]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-dispatchers/-default.html
[GlobalScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-global-scope/index.html
[withContext]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/with-context.html
[CoroutineScope()]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-coroutine-scope.html
[CoroutineScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-coroutine-scope/index.html
[CompletableDeferred]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-completable-deferred/index.html
<!--- INDEX kotlinx.coroutines.sync -->
[Mutex]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.sync/-mutex/index.html
[Mutex.lock]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.sync/-mutex/lock.html
[Mutex.unlock]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.sync/-mutex/unlock.html
[withLock]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.sync/with-lock.html
<!--- INDEX kotlinx.coroutines.channels -->
[actor]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/actor.html
[produce]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/produce.html
<!--- END -->
