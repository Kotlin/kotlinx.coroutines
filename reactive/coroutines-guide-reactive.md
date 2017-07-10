<!--- INCLUDE .*/example-reactive-([a-z]+)-([0-9]+)\.kt 
/*
 * Copyright 2016-2017 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// This file was automatically generated from coroutines-guide-reactive.md by Knit tool. Do not edit.
package guide.reactive.$$1.example$$2

-->
<!--- KNIT     kotlinx-coroutines-rx2/src/test/kotlin/guide/.*\.kt -->
<!--- TEST_OUT kotlinx-coroutines-rx2/src/test/kotlin/guide/test/GuideReactiveTest.kt
// This file was automatically generated from coroutines-guide-reactive.md by Knit tool. Do not edit.
package guide.test

import org.junit.Test

class GuideReactiveTest {
-->

# Guide to reactive streams with coroutines

This guide explains key differences between Kotlin coroutines and reactive streams and shows 
how they can be used together for greater good. Prior familiarity with basic coroutine concepts
that are covered in [Guide to kotlinx.coroutines](../coroutines-guide.md) is not required, 
but is a big plus. If you are familiar with reactive streams, you may find this guide
a better introduction into the world of coroutines.

There are several modules in `kotlinx.coroutines` project that are related to reactive streams:

* [kotlinx-coroutines-reactive](kotlinx-coroutines-reactive) -- utilities for [Reactive Streams](http://www.reactive-streams.org)
* [kotlinx-coroutines-reactor](kotlinx-coroutines-reactor) -- utilities for [Reactor](https://projectreactor.io)
* [kotlinx-coroutines-rx1](kotlinx-coroutines-rx1) -- utilities for [RxJava 1.x](https://github.com/ReactiveX/RxJava/tree/1.x)
* [kotlinx-coroutines-rx2](kotlinx-coroutines-rx2) -- utilities for [RxJava 2.x](https://github.com/ReactiveX/RxJava)

This guide is mostly based on [Reactive Streams](http://www.reactive-streams.org) specification and uses
its `Publisher` interface with some examples based on [RxJava 2.x](https://github.com/ReactiveX/RxJava),
which implements reactive streams specification.

You are welcome to clone 
[`kotlinx.coroutines` project](https://github.com/Kotlin/kotlinx.coroutines)
from GitHub to your workstation in order to
run all the presented examples. They are contained in 
[reactive/kotlinx-coroutines-rx2/src/test/kotlin/guide](kotlinx-coroutines-rx2/src/test/kotlin/guide)
directory of the project.
 
## Table of contents

<!--- TOC -->

* [Differences between reactive streams and channels](#differences-between-reactive-streams-and-channels)
  * [Basics of iteration](#basics-of-iteration)
  * [Subscription and cancellation](#subscription-and-cancellation)
  * [Backpressure](#backpressure)
  * [Rx Subject vs BroadcastChannel](#rx-subject-vs-broadcastchannel)
* [Operators](#operators)
  * [Range](#range)
  * [Fused filter-map hybrid](#fused-filter-map-hybrid)
  * [Take until](#take-until)
  * [Merge](#merge)
* [Coroutine context](#coroutine-context)
  * [Threads with Rx](#threads-with-rx)
  * [Threads with coroutines](#threads-with-coroutines)
  * [Rx observeOn](#rx-observeon)
  * [Coroutine context to rule them all](#coroutine-context-to-rule-them-all)
  * [Unconfined context](#unconfined-context)

<!--- END_TOC -->

## Differences between reactive streams and channels

This section outlines key differences between reactive streams and coroutine-based channels. 

### Basics of iteration

The [Channel] is somewhat similar concept to the following reactive stream classes:

* Reactive stream [Publisher](https://github.com/reactive-streams/reactive-streams-jvm/blob/master/api/src/main/java/org/reactivestreams/Publisher.java);
* Rx Java 1.x [Observable](http://reactivex.io/RxJava/javadoc/rx/Observable.html);
* Rx Java 2.x [Flowable](http://reactivex.io/RxJava/2.x/javadoc/), which implements `Publisher`.

They all describe an asynchronous stream of elements (aka items in Rx), either infinite or finite, 
and all of them support backpressure.
  
However, the `Channel` always represents a _hot_ stream of items, using Rx terminology. Elements are being sent
into the channel by producer coroutines and are received from it by consumer coroutines. 
Every [receive][ReceiveChannel.receive] invocation consumes an element from the channel. 
Let us illustrate it with the following example:

<!--- INCLUDE
import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.channels.*
-->

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    // create a channel that produces numbers from 1 to 3 with 200ms delays between them
    val source = produce<Int>(context) {
        println("Begin") // mark the beginning of this coroutine in output
        for (x in 1..3) {
            delay(200) // wait for 200ms
            send(x) // send number x to the channel
        }
    }
    // print elements from the source
    println("Elements:")
    source.consumeEach { // consume elements from it
        println(it)
    }
    // print elements from the source AGAIN
    println("Again:")
    source.consumeEach { // consume elements from it
        println(it)
    }
}
```

> You can get full code [here](kotlinx-coroutines-rx2/src/test/kotlin/guide/example-reactive-basic-01.kt)

This code produces the following output: 

```text
Elements:
Begin
1
2
3
Again:
```

<!--- TEST -->

Notice, how "Begin" line was printed just once, because [produce] _coroutine builder_, when it is executed,
launches one coroutine to produce a stream of elements. All the produced elements are consumed 
with [ReceiveChannel.consumeEach][consumeEach] 
extension function. There is no way to receive the elements from this
channel again. The channel is closed when the producer coroutine is over and the attempt to receive 
from it again cannot receive anything.

Let us rewrite this code using [publish] coroutine builder from `kotlinx-coroutines-reactive` module
instead of [produce] from `kotlinx-coroutines-core` module. The code stays the same, 
but where `source` used to have [ReceiveChannel] type, it now has reactive streams 
[Publisher](http://www.reactive-streams.org/reactive-streams-1.0.0-javadoc/org/reactivestreams/Publisher.html) 
type.

<!--- INCLUDE
import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.reactive.*
-->

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    // create a publisher that produces numbers from 1 to 3 with 200ms delays between them
    val source = publish<Int>(context) {  
    //           ^^^^^^^  <---  Difference from the previous examples is here
        println("Begin") // mark the beginning of this coroutine in output
        for (x in 1..3) {
            delay(200) // wait for 200ms
            send(x) // send number x to the channel
        }
    }
    // print elements from the source
    println("Elements:")
    source.consumeEach { // consume elements from it
        println(it)
    }
    // print elements from the source AGAIN
    println("Again:")
    source.consumeEach { // consume elements from it
        println(it)
    }
}
```

> You can get full code [here](kotlinx-coroutines-rx2/src/test/kotlin/guide/example-reactive-basic-02.kt)

Now the output of this code changes to:

```text
Elements:
Begin
1
2
3
Again:
Begin
1
2
3
```

<!--- TEST -->

This example highlights the key difference between a reactive stream and a channel. A reactive stream is a higher-order
functional concept. While the channel _is_ a stream of elements, the reactive stream defines a recipe on how the stream of 
elements is produced. It becomes the actual stream of elements on _subscription_. Each subscriber may receive the same or
a different stream of elements, depending on how the corresponding implementation of `Publisher` works.

The [publish] coroutine builder, that is used in the above example, launches a fresh coroutine on each subscription.
Every [Publisher.consumeEach][org.reactivestreams.Publisher.consumeEach] invocation creates a fresh subscription.
We have two of them in this code and that is why we see "Begin" printed twice. 

In Rx lingo this is called a _cold_ publisher. Many standard Rx operators produce cold streams, too. We can iterate
over them from a coroutine, and every subscription produces the same stream of elements.

> Note, that we can replicate the same behaviour that we saw with channels by using Rx 
[publish](http://reactivex.io/RxJava/2.x/javadoc/io/reactivex/Flowable.html#publish()) 
operator and [connect](http://reactivex.io/RxJava/2.x/javadoc/io/reactivex/flowables/ConnectableFlowable.html#connect())
method with it.

### Subscription and cancellation

An example in the previous section uses `source.consumeEach { ... }` snippet to open a subscription 
and receive all the elements from it. If we need more control on how what to do with 
the elements that are being received from the channel, we can use [Publisher.open][org.reactivestreams.Publisher.open]
as shown in the following example:

<!--- INCLUDE
import io.reactivex.*
import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.reactive.*
-->

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    val source = Flowable.range(1, 5) // a range of five numbers
        .doOnSubscribe { println("OnSubscribe") } // provide some insight
        .doFinally { println("Finally") }         // ... into what's going on
    var cnt = 0 
    source.open().use { channel -> // open channel to the source
        for (x in channel) { // iterate over the channel to receive elements from it
            println(x)
            if (++cnt >= 3) break // break when 3 elements are printed
        }
        // `use` will close the channel when this block of code is complete
    }
}
```

> You can get full code [here](kotlinx-coroutines-rx2/src/test/kotlin/guide/example-reactive-basic-03.kt)

It produces the following output:
 
```text
OnSubscribe
1
2
3
Finally
```

<!--- TEST -->
 
With an explicit `open` we should [close][SubscriptionReceiveChannel.close] the corresponding 
subscription to unsubscribe from the source. However, instead of invoking `close` explicitly, 
this code relies on [use](https://kotlinlang.org/api/latest/jvm/stdlib/kotlin.io/use.html)
function from Kotlin's standard library.
The installed 
[doFinally](http://reactivex.io/RxJava/2.x/javadoc/io/reactivex/Flowable.html#doFinally(io.reactivex.functions.Action))
listener prints "Finally" to confirm that the subscription is actually being closed.
 
We do not need to use an explicit `close` if iteration is performed over all the items that are emitted 
by the publisher, because it is being closed automatically by `consumeEach`:

<!--- INCLUDE
import io.reactivex.*
import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.reactive.*
-->

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    val source = Flowable.range(1, 5) // a range of five numbers
        .doOnSubscribe { println("OnSubscribe") } // provide some insight
        .doFinally { println("Finally") }         // ... into what's going on
    // iterate over the source fully
    source.consumeEach { println(it) }
}
```

> You can get full code [here](kotlinx-coroutines-rx2/src/test/kotlin/guide/example-reactive-basic-04.kt)

We get the following output:

```text
OnSubscribe
1
2
3
4
Finally
5
```

<!--- TEST -->

Notice, how "Finally" is printed before the last element "5". It happens because our `main` function in this
example is a coroutine that we start with [runBlocking] coroutine builder.
Our main coroutine receives on the channel using `source.consumeEach { ... }` expression.
The main coroutine is _suspended_ while it waits for the source to emit an item.
When the last item is emitted by `Flowable.range(1, 5)` it
_resumes_ the main coroutine, which gets dispatched onto the main thread to print this
 last element at a later point in time, while the source completes and prints "Finally".

### Backpressure

Backpressure is one of the most interesting and complex aspects of reactive streams. Coroutines can 
_suspend_ and they provide a natural answer to handling backpressure. 

In Rx Java 2.x a backpressure-capable class is called 
[Flowable](http://reactivex.io/RxJava/2.x/javadoc/io/reactivex/Flowable.html).
In the following example we use [rxFlowable] coroutine builder from `kotlinx-coroutines-rx2` module to define a 
flowable that sends three integers from 1 to 3. 
It prints a message to the output before invocation of
suspending [send][SendChannel.send] function, so that we can study how it operates.

The integers are generated in the context of the main thread, but subscription is shifted 
to another thread using Rx
[observeOn](http://reactivex.io/RxJava/2.x/javadoc/io/reactivex/Flowable.html#observeOn(io.reactivex.Scheduler,%20boolean,%20int))
operator with a buffer of size 1. 
The subscriber is slow. It takes 500 ms to process each item, which is simulated using `Thread.sleep`.

<!--- INCLUDE
import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.rx2.rxFlowable
import io.reactivex.schedulers.Schedulers
-->

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> { 
    // coroutine -- fast producer of elements in the context of the main thread
    val source = rxFlowable(context) {
        for (x in 1..3) {
            send(x) // this is a suspending function
            println("Sent $x") // print after successfully sent item
        }
    }
    // subscribe on another thread with a slow subscriber using Rx
    source
        .observeOn(Schedulers.io(), false, 1) // specify buffer size of 1 item
        .doOnComplete { println("Complete") }
        .subscribe { x ->
            Thread.sleep(500) // 500ms to process each item
            println("Processed $x")
        }
    delay(2000) // suspend the main thread for a few seconds
}
```

> You can get full code [here](kotlinx-coroutines-rx2/src/test/kotlin/guide/example-reactive-basic-05.kt)

The output of this code nicely illustrates how backpressure works with coroutines:

```text
Sent 1
Processed 1
Sent 2
Processed 2
Sent 3
Processed 3
Complete
```

<!--- TEST -->

We see here how producer coroutine puts the first element in the buffer and is suspended while trying to send another 
one. Only after consumer processes the first item, producer sends the second one and resumes, etc.


### Rx Subject vs BroadcastChannel
 
RxJava has a concept of [Subject](https://github.com/ReactiveX/RxJava/wiki/Subject) which is an object that
effectively broadcasts elements to all its subscribers. The matching concept in coroutines world is called a 
[BroadcastChannel]. There is a variety of subjects in Rx with 
[BehaviorSubject](http://reactivex.io/RxJava/2.x/javadoc/io/reactivex/subjects/BehaviorSubject.html) being
the one used to manage state:

<!--- INCLUDE
import io.reactivex.subjects.BehaviorSubject
-->

```kotlin
fun main(args: Array<String>) {
    val subject = BehaviorSubject.create<String>()
    subject.onNext("one")
    subject.onNext("two") // updates the state of BehaviorSubject, "one" value is lost
    // now subscribe to this subject and print everything
    subject.subscribe(System.out::println)
    subject.onNext("three")
    subject.onNext("four")
}
```

> You can get full code [here](kotlinx-coroutines-rx2/src/test/kotlin/guide/example-reactive-basic-06.kt)

This code prints the current state of the subject on subscription and all its further updates:


```text
two
three
four
```

<!--- TEST -->

You can subscribe to subjects from a coroutine just as with any other reactive stream:
   
<!--- INCLUDE 
import io.reactivex.subjects.BehaviorSubject
import kotlinx.coroutines.experimental.Unconfined
import kotlinx.coroutines.experimental.launch
import kotlinx.coroutines.experimental.runBlocking
import kotlinx.coroutines.experimental.rx2.consumeEach
-->   
   
```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    val subject = BehaviorSubject.create<String>()
    subject.onNext("one")
    subject.onNext("two")
    // now launch a coroutine to print everything
    launch(Unconfined) { // launch coroutine in unconfined context
        subject.consumeEach { println(it) }
    }
    subject.onNext("three")
    subject.onNext("four")
}
```   

> You can get full code [here](kotlinx-coroutines-rx2/src/test/kotlin/guide/example-reactive-basic-07.kt)

The result is the same:

```text
two
three
four
```

<!--- TEST -->

Here we use [Unconfined] coroutine context to launch consuming coroutine with the same behaviour as subscription in Rx. 
It basically means that the launched coroutine is going to be immediately executed in the same thread that 
is emitting elements. Contexts are covered in more details in a [separate section](#coroutine-context).

The advantage of coroutines is that it is easy to get conflation behavior for single-threaded UI updates. 
A typical UI application does not need to react to every state change. Only the most recent state is relevant.
A sequence of back-to-back updates to the application state needs to get reflected in UI only once, 
as soon as the UI thread is free. For the following example we are going to simulate this by launching 
consuming coroutine in the context of the main thread and use [yield] function to simulate a break in the 
sequence of updates and to release the main thread:

<!--- INCLUDE
import io.reactivex.subjects.BehaviorSubject
import kotlinx.coroutines.experimental.launch
import kotlinx.coroutines.experimental.runBlocking
import kotlinx.coroutines.experimental.rx2.consumeEach
import kotlinx.coroutines.experimental.yield
-->

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    val subject = BehaviorSubject.create<String>()
    subject.onNext("one")
    subject.onNext("two")
    // now launch a coroutine to print the most recent update
    launch(context) { // use the context of the main thread for a coroutine
        subject.consumeEach { println(it) }
    }
    subject.onNext("three")
    subject.onNext("four")
    yield() // yield the main thread to the launched coroutine <--- HERE
}
```

> You can get full code [here](kotlinx-coroutines-rx2/src/test/kotlin/guide/example-reactive-basic-08.kt)

Now coroutine process (prints) only the most recent update:

```text
four
```

<!--- TEST -->

The corresponding behavior in a pure coroutines world is implemented by [ConflatedBroadcastChannel] 
that provides the same logic on top of coroutine channels directly, 
without going through the bridge to the reactive streams:

<!--- INCLUDE
import kotlinx.coroutines.experimental.channels.ConflatedBroadcastChannel
import kotlinx.coroutines.experimental.channels.consumeEach
import kotlinx.coroutines.experimental.launch
import kotlinx.coroutines.experimental.runBlocking
import kotlinx.coroutines.experimental.yield
-->

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    val broadcast = ConflatedBroadcastChannel<String>()
    broadcast.offer("one")
    broadcast.offer("two")
    // now launch a coroutine to print the most recent update
    launch(context) { // use the context of the main thread for a coroutine
        broadcast.consumeEach { println(it) }
    }
    broadcast.offer("three")
    broadcast.offer("four")
    yield() // yield the main thread to the launched coroutine
}
```

> You can get full code [here](kotlinx-coroutines-rx2/src/test/kotlin/guide/example-reactive-basic-09.kt)

It produces the same output as the previous example based on `BehaviorSubject`:

```text
four
```

<!--- TEST -->

Another implementation of [BroadcastChannel] is [ArrayBroadcastChannel]. It delivers every event to every
subscriber since the moment the corresponding subscription is open. It corresponds to 
[PublishSubject][http://reactivex.io/RxJava/2.x/javadoc/io/reactivex/subjects/PublishSubject.html] in Rx.
The capacity of the buffer in the constructor of `ArrayBroadcastChannel` controls the numbers of elements
that can be sent before the sender is suspended waiting for receiver to receive those elements.

## Operators

Full-featured reactive stream libraries, like Rx, come with 
[a very large set of operators](http://reactivex.io/documentation/operators.html) to create, transform, combine
and otherwise process the corresponding streams. Creating your own operators with support for
back-pressure is [notoriously](http://akarnokd.blogspot.ru/2015/05/pitfalls-of-operator-implementations.html)
[difficult](https://github.com/ReactiveX/RxJava/wiki/Writing-operators-for-2.0).

Coroutines and channels are designed to provide an opposite experience. There are no built-in operators, 
but processing streams of elements is extremely simple and back-pressure is supported automatically 
without you having to explicitly think about it.

This section shows coroutine-based implementation of several reactive stream operators.  

### Range

Let's roll out own implementation of 
[range](http://reactivex.io/RxJava/2.x/javadoc/io/reactivex/Flowable.html#range(int,%20int))
operator for reactive streams `Publisher` interface. The asynchronous clean-slate implementation of this operator for
reactive streams is explained in 
[this blog post](http://akarnokd.blogspot.ru/2017/03/java-9-flow-api-asynchronous-integer.html).
It takes a lot of code.
Here is the corresponding code with coroutines:

<!--- INCLUDE
import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.reactive.*
import kotlin.coroutines.experimental.CoroutineContext
-->

```kotlin
fun range(context: CoroutineContext, start: Int, count: Int) = publish<Int>(context) {
    for (x in start until start + count) send(x)
}
```

In this code `CoroutineContext` is used instead of an `Executor` and all the backpressure aspects are taken care
of by the coroutines machinery. Note, that this implementation depends only on the small reactive streams library
that defines `Publisher` interface and its friends.

It is straightforward to use from a coroutine:

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    range(CommonPool, 1, 5).consumeEach { println(it) }
}
```

> You can get full code [here](kotlinx-coroutines-rx2/src/test/kotlin/guide/example-reactive-operators-01.kt)

The result of this code is quite expected:
   
```text
1
2
3
4
5
```

<!--- TEST -->

### Fused filter-map hybrid

Reactive operators like 
[filter](http://reactivex.io/RxJava/2.x/javadoc/io/reactivex/Flowable.html#filter(io.reactivex.functions.Predicate)) and 
[map](http://reactivex.io/RxJava/2.x/javadoc/io/reactivex/Flowable.html#map(io.reactivex.functions.Function))
are trivial to implement with coroutines. For a bit of challenge and showcase, let us combine them
into the single `fusedFilterMap` operator: 

<!--- INCLUDE
import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.reactive.*
import org.reactivestreams.Publisher
import kotlin.coroutines.experimental.CoroutineContext
-->

```kotlin
fun <T, R> Publisher<T>.fusedFilterMap(
    context: CoroutineContext,   // the context to execute this coroutine in
    predicate: (T) -> Boolean,   // the filter predicate
    mapper: (T) -> R             // the mapper function
) = publish<R>(context) {
    consumeEach {                // consume the source stream 
        if (predicate(it))       // filter part
            send(mapper(it))     // map part
    }        
}
```

Using `range` from the previous example we can test our `fusedFilterMap` 
by filtering for even numbers and mapping them to strings:

<!--- INCLUDE

fun range(context: CoroutineContext, start: Int, count: Int) = publish<Int>(context) {
    for (x in start until start + count) send(x)
}
-->

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
   range(context, 1, 5)
       .fusedFilterMap(context, { it % 2 == 0}, { "$it is even" })
       .consumeEach { println(it) } // print all the resulting strings
}
```

> You can get full code [here](kotlinx-coroutines-rx2/src/test/kotlin/guide/example-reactive-operators-02.kt)

It is not hard to see, that the result is going to be:

```text
2 is even
4 is even
```

<!--- TEST -->

### Take until

Let's implement our own version of
[takeUntil](http://reactivex.io/RxJava/2.x/javadoc/io/reactivex/Flowable.html#takeUntil(org.reactivestreams.Publisher))
operator. It is quite a [tricky one](http://akarnokd.blogspot.ru/2015/05/pitfalls-of-operator-implementations.html) 
to implement, because of the need to track and manage subscription to two streams. 
We need to relay all the elements from the source stream until the other stream either completes or 
emits anything. However, we have [select] expression to rescue us in coroutines implementation:

<!--- INCLUDE
import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.reactive.*
import org.reactivestreams.Publisher
import kotlin.coroutines.experimental.CoroutineContext
import kotlinx.coroutines.experimental.selects.whileSelect
-->

```kotlin
fun <T, U> Publisher<T>.takeUntil(context: CoroutineContext, other: Publisher<U>) = publish<T>(context) {
    this@takeUntil.open().use { thisChannel ->           // explicitly open channel to Publisher<T>
        other.open().use { otherChannel ->               // explicitly open channel to Publisher<U>
            whileSelect {
                otherChannel.onReceive { false }         // bail out on any received element from `other`
                thisChannel.onReceive { send(it); true } // resend element from this channel and continue
            }
        }
    }
}
```

This code is using [whileSelect] as a nicer shortcut to `while(select{...}) {}` loop and Kotlin's
[use](https://kotlinlang.org/api/latest/jvm/stdlib/kotlin.io/use.html) 
expression to close the channels on exit, which unsubscribes from the corresponding publishers. 

The following hand-written combination of 
[range](http://reactivex.io/RxJava/2.x/javadoc/io/reactivex/Flowable.html#range(int,%20int)) with 
[interval](http://reactivex.io/RxJava/2.x/javadoc/io/reactivex/Flowable.html#interval(long,%20java.util.concurrent.TimeUnit,%20io.reactivex.Scheduler))
is used for testing. It is coded using a `publish` coroutine builder 
(its pure-Rx implementation is shown in later sections):

```kotlin
fun rangeWithInterval(context: CoroutineContext, time: Long, start: Int, count: Int) = publish<Int>(context) {
    for (x in start until start + count) { 
        delay(time) // wait before sending each number
        send(x)
    }
}
```

The following code shows how `takeUntil` works: 

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    val slowNums = rangeWithInterval(context, 200, 1, 10)         // numbers with 200ms interval
    val stop = rangeWithInterval(context, 500, 1, 10)             // the first one after 500ms
    slowNums.takeUntil(context, stop).consumeEach { println(it) } // let's test it
}
```

> You can get full code [here](kotlinx-coroutines-rx2/src/test/kotlin/guide/example-reactive-operators-03.kt)

Producing 

```text
1
2
```

<!--- TEST -->

### Merge

There are always at least two ways for processing multiple streams of data with coroutines. One way involving
[select] was shown in the previous example. The other way is just to launch multiple coroutines. Let
us implement 
[merge](http://reactivex.io/RxJava/2.x/javadoc/io/reactivex/Flowable.html#merge(org.reactivestreams.Publisher))
operator using the later approach:

<!--- INCLUDE
import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.reactive.*
import org.reactivestreams.Publisher
import kotlin.coroutines.experimental.CoroutineContext
-->

```kotlin
fun <T> Publisher<Publisher<T>>.merge(context: CoroutineContext) = publish<T>(context) {
  consumeEach { pub ->                 // for each publisher received on the source channel
      launch(this.context) {           // launch a child coroutine
          pub.consumeEach { send(it) } // resend all element from this publisher
      }
  }
}
```

Notice, the use of `this.context` in the invocation of [launch] coroutine builder. It is used to refer
to the [CoroutineScope.context] that is provided by [publish] builder. This way, all the coroutines that are
being launched here are [children](../coroutines-guide.md#children-of-a-coroutine) of the `publish`
coroutine and will get cancelled when the `publish` coroutine is cancelled or is otherwise completed. 
This implementation completes as soon as the original publisher completes. 

For a test, let us start with `rangeWithInterval` function from the previous example and write a 
producer that sends its results twice with some delay:

<!--- INCLUDE

fun rangeWithInterval(context: CoroutineContext, time: Long, start: Int, count: Int) = publish<Int>(context) {
    for (x in start until start + count) { 
        delay(time) // wait before sending each number
        send(x)
    }
}
-->

```kotlin
fun testPub(context: CoroutineContext) = publish<Publisher<Int>>(context) {
    send(rangeWithInterval(context, 250, 1, 4)) // number 1 at 250ms, 2 at 500ms, 3 at 750ms, 4 at 1000ms 
    delay(100) // wait for 100 ms
    send(rangeWithInterval(context, 500, 11, 3)) // number 11 at 600ms, 12 at 1100ms, 13 at 1600ms
    delay(1100) // wait for 1.1s - done in 1.2 sec after start
}
```

The test code is to use `merge` on `testPub` and to display the results:

```kotlin
fun main(args: Array<String>) = runBlocking<Unit> {
    testPub(context).merge(context).consumeEach { println(it) } // print the whole stream
}
```

> You can get full code [here](kotlinx-coroutines-rx2/src/test/kotlin/guide/example-reactive-operators-04.kt)

And the results should be: 

```text
1
2
11
3
4
12
```

<!--- TEST -->

## Coroutine context

All the example operators that are shown in the previous section have an explicit
[CoroutineContext](https://kotlinlang.org/api/latest/jvm/stdlib/kotlin.coroutines.experimental/-coroutine-context/) 
parameter. In Rx world it roughly corresponds to 
a [Scheduler](http://reactivex.io/RxJava/2.x/javadoc/io/reactivex/Scheduler.html).

### Threads with Rx

The following example shows the basics of threading context management with Rx.
Here `rangeWithIntervalRx` is an implementation of `rangeWithInterval` function using Rx 
`zip`, `range`, and `interval` operators.

<!--- INCLUDE
import io.reactivex.*
import io.reactivex.functions.BiFunction
import io.reactivex.schedulers.Schedulers
import java.util.concurrent.TimeUnit
-->

```kotlin
fun rangeWithIntervalRx(scheduler: Scheduler, time: Long, start: Int, count: Int): Flowable<Int> = 
    Flowable.zip(
        Flowable.range(start, count),
        Flowable.interval(time, TimeUnit.MILLISECONDS, scheduler),
        BiFunction { x, _ -> x })

fun main(args: Array<String>) {
    rangeWithIntervalRx(Schedulers.computation(), 100, 1, 3)
        .subscribe { println("$it on thread ${Thread.currentThread().name}") }
    Thread.sleep(1000)
}
```

> You can get full code [here](kotlinx-coroutines-rx2/src/test/kotlin/guide/example-reactive-context-01.kt)

We are explicitly passing the 
[Schedulers.computation()](http://reactivex.io/RxJava/2.x/javadoc/io/reactivex/schedulers/Schedulers.html#computation()) 
scheduler to our `rangeWithIntervalRx` operator and
it is going to be executed in Rx computation thread pool. The output is going to be similar to the following one:

```text
1 on thread RxComputationThreadPool-1
2 on thread RxComputationThreadPool-1
3 on thread RxComputationThreadPool-1
```

<!--- TEST FLEXIBLE_THREAD -->

### Threads with coroutines

In the world of coroutines `Schedulers.computation()` roughly corresponds to [CommonPool], 
so the previous example is similar to the following one:

<!--- INCLUDE
import io.reactivex.*
import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.reactive.*
import kotlin.coroutines.experimental.CoroutineContext
-->

```kotlin
fun rangeWithInterval(context: CoroutineContext, time: Long, start: Int, count: Int) = publish<Int>(context) {
    for (x in start until start + count) { 
        delay(time) // wait before sending each number
        send(x)
    }
}

fun main(args: Array<String>) {
    Flowable.fromPublisher(rangeWithInterval(CommonPool, 100, 1, 3))
        .subscribe { println("$it on thread ${Thread.currentThread().name}") }
    Thread.sleep(1000)
}
```

> You can get full code [here](kotlinx-coroutines-rx2/src/test/kotlin/guide/example-reactive-context-02.kt)

The produced output is going to be similar to:

```text
1 on thread ForkJoinPool.commonPool-worker-1
2 on thread ForkJoinPool.commonPool-worker-1
3 on thread ForkJoinPool.commonPool-worker-1
```

<!--- TEST LINES_START -->

Here we've used Rx 
[subscribe](http://reactivex.io/RxJava/2.x/javadoc/io/reactivex/Flowable.html#subscribe(io.reactivex.functions.Consumer))
operator that does not have its own scheduler and operates on the same thread that the publisher -- on a `CommonPool`
in this example.

### Rx observeOn 

In Rx you use special operators to modify the threading context for operations in the chain. You
can find some [good guides](http://tomstechnicalblog.blogspot.ru/2016/02/rxjava-understanding-observeon-and.html)
about them, if you are not familiar. 

For example, there is
[observeOn](http://reactivex.io/RxJava/2.x/javadoc/io/reactivex/Flowable.html#observeOn(io.reactivex.Scheduler)) 
operator. Let us modify the previous example to observe using `Schedulers.computation()`:   

<!--- INCLUDE
import io.reactivex.*
import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.reactive.*
import io.reactivex.schedulers.Schedulers
import kotlin.coroutines.experimental.CoroutineContext
-->

```kotlin
fun rangeWithInterval(context: CoroutineContext, time: Long, start: Int, count: Int) = publish<Int>(context) {
    for (x in start until start + count) { 
        delay(time) // wait before sending each number
        send(x)
    }
}

fun main(args: Array<String>) {
    Flowable.fromPublisher(rangeWithInterval(CommonPool, 100, 1, 3))
        .observeOn(Schedulers.computation())                           // <-- THIS LINE IS ADDED
        .subscribe { println("$it on thread ${Thread.currentThread().name}") }
    Thread.sleep(1000)
}
```

> You can get full code [here](kotlinx-coroutines-rx2/src/test/kotlin/guide/example-reactive-context-03.kt)

Here is the difference in output, notice "RxComputationThreadPool":

```text
1 on thread RxComputationThreadPool-1
2 on thread RxComputationThreadPool-1
3 on thread RxComputationThreadPool-1
```

<!--- TEST FLEXIBLE_THREAD -->

### Coroutine context to rule them all

A coroutine is always working in some context. For example, let us start a coroutine
in the main thread with [runBlocking] and iterate over the result of the Rx version of `rangeWithIntervalRx` operator, 
instead of using Rx `subscribe` operator:

<!--- INCLUDE
import io.reactivex.*
import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.reactive.*
import io.reactivex.functions.BiFunction
import io.reactivex.schedulers.Schedulers
import java.util.concurrent.TimeUnit
-->

```kotlin
fun rangeWithIntervalRx(scheduler: Scheduler, time: Long, start: Int, count: Int): Flowable<Int> =
    Flowable.zip(
        Flowable.range(start, count),
        Flowable.interval(time, TimeUnit.MILLISECONDS, scheduler),
        BiFunction { x, _ -> x })

fun main(args: Array<String>) = runBlocking<Unit> {
    rangeWithIntervalRx(Schedulers.computation(), 100, 1, 3)
        .consumeEach { println("$it on thread ${Thread.currentThread().name}") }
}
```

> You can get full code [here](kotlinx-coroutines-rx2/src/test/kotlin/guide/example-reactive-context-04.kt)

The resulting messages are going to be printed in the main thread:

```text
1 on thread main
2 on thread main
3 on thread main
```

<!--- TEST LINES_START -->

### Unconfined context

Most Rx operators do not have any specific thread (scheduler) associated with them and are working 
in whatever thread that they happen to be invoked in. We've seen it on the example of `subscribe` operator 
in the [threads with Rx](#threads-with-rx) section.
 
In the world of coroutines, [Unconfined] context serves a similar role. Let us modify our previous example,
but instead of iterating over the source `Flowable` from the `runBlocking` coroutine that is confined 
to the main thread, we launch a new coroutine in `Unconfined` context, while the main coroutine
simply waits its completion using [Job.join]:

<!--- INCLUDE
import io.reactivex.*
import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.reactive.*
import io.reactivex.functions.BiFunction
import io.reactivex.schedulers.Schedulers
import java.util.concurrent.TimeUnit
-->

```kotlin
fun rangeWithIntervalRx(scheduler: Scheduler, time: Long, start: Int, count: Int): Flowable<Int> =
    Flowable.zip(
        Flowable.range(start, count),
        Flowable.interval(time, TimeUnit.MILLISECONDS, scheduler),
        BiFunction { x, _ -> x })

fun main(args: Array<String>) = runBlocking<Unit> {
    val job = launch(Unconfined) { // launch new coroutine in Unconfined context (without its own thread pool)
        rangeWithIntervalRx(Schedulers.computation(), 100, 1, 3)
            .consumeEach { println("$it on thread ${Thread.currentThread().name}") }
    }
    job.join() // wait for our coroutine to complete
}
```

> You can get full code [here](kotlinx-coroutines-rx2/src/test/kotlin/guide/example-reactive-context-05.kt)

Now, the output shows that the code of the coroutine is executing in the Rx computation thread pool, just
like our initial example using Rx `subscribe` operator.

```text
1 on thread RxComputationThreadPool-1
2 on thread RxComputationThreadPool-1
3 on thread RxComputationThreadPool-1
```

<!--- TEST LINES_START -->

Note, that [Unconfined] context shall be used with care. It may improve the overall performance on certain tests,
due to the increased stack-locality of operations and less scheduling overhead, but it also produces deeper stacks 
and makes it harder to reason about asynchronicity of the code that is using it. 

If a coroutine sends an element to a channel, then the thread that invoked the 
[send][SendChannel.send] may start executing the code of a coroutine with [Unconfined] dispatcher.
The original producer coroutine that invoked `send`  is paused until the unconfined consumer coroutine hits its next
suspension point. This is very similar to a lock-step single-threaded `onNext` execution in Rx world in the absense
of thread-shifting operators. It is a normal default for Rx, because operators are usually doing very small chunks
of work and you have to combine many operators for a complex processing. However, this is unusual with coroutines, 
where you can have an arbitrary complex processing in a coroutine. Usually, you only need to chain stream-processing
coroutines for complex pipelines with fan-in and fan-out between multiple worker coroutines.

<!--- MODULE kotlinx-coroutines-core -->
<!--- INDEX kotlinx.coroutines.experimental -->
[runBlocking]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/run-blocking.html
[Unconfined]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-unconfined/index.html
[yield]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/yield.html
[launch]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/launch.html
[CoroutineScope.context]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-coroutine-scope/context.html
[CommonPool]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-common-pool/index.html
[Job.join]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-job/join.html
<!--- INDEX kotlinx.coroutines.experimental.channels -->
[Channel]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.channels/-channel/index.html
[ReceiveChannel.receive]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.channels/-receive-channel/receive.html
[produce]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.channels/produce.html
[consumeEach]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.channels/consume-each.html
[ReceiveChannel]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.channels/-receive-channel/index.html
[SubscriptionReceiveChannel.close]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.channels/-subscription-receive-channel/close.html
[SendChannel.send]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.channels/-send-channel/send.html
[BroadcastChannel]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.channels/-broadcast-channel/index.html
[ConflatedBroadcastChannel]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.channels/-conflated-broadcast-channel/index.html
[ArrayBroadcastChannel]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.channels/-array-broadcast-channel/index.html
<!--- INDEX kotlinx.coroutines.experimental.selects -->
[select]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.selects/select.html
[whileSelect]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.selects/while-select.html
<!--- MODULE kotlinx-coroutines-reactive -->
<!--- INDEX kotlinx.coroutines.experimental.reactive -->
[publish]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-reactive/kotlinx.coroutines.experimental.reactive/publish.html
[org.reactivestreams.Publisher.consumeEach]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-reactive/kotlinx.coroutines.experimental.reactive/org.reactivestreams.-publisher/consume-each.html
[org.reactivestreams.Publisher.open]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-reactive/kotlinx.coroutines.experimental.reactive/org.reactivestreams.-publisher/open.html
<!--- MODULE kotlinx-coroutines-rx2 -->
<!--- INDEX kotlinx.coroutines.experimental.rx2 -->
[rxFlowable]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx2/kotlinx.coroutines.experimental.rx2/rx-flowable.html
<!--- END -->


