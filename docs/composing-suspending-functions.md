<!--- INCLUDE .*/example-([a-z]+)-([0-9a-z]+)\.kt 
/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

// This file was automatically generated from coroutines-guide.md by Knit tool. Do not edit.
package kotlinx.coroutines.guide.$$1$$2
-->
<!--- KNIT     ../core/kotlinx-coroutines-core/test/guide/.*\.kt -->
<!--- TEST_OUT ../core/kotlinx-coroutines-core/test/guide/test/ComposingGuideTest.kt
// This file was automatically generated from coroutines-guide.md by Knit tool. Do not edit.
package kotlinx.coroutines.guide.test

import org.junit.Test

class ComposingGuideTest {
--> 

**Table of contents**

<!--- TOC -->

* [Composing suspending functions](#composing-suspending-functions)
  * [Sequential by default](#sequential-by-default)
  * [Concurrent using async](#concurrent-using-async)
  * [Lazily started async](#lazily-started-async)
  * [Async-style functions](#async-style-functions)
  * [Structured concurrency with async](#structured-concurrency-with-async)

<!--- END_TOC -->

## Composing suspending functions

This section covers various approaches to composition of suspending functions.

### Sequential by default

Assume that we have two suspending functions defined elsewhere that do something useful like some kind of 
remote service call or computation. We just pretend they are useful, but actually each one just
delays for a second for the purpose of this example:

<div class="sample" markdown="1" theme="idea" data-highlight-only>

```kotlin
suspend fun doSomethingUsefulOne(): Int {
    delay(1000L) // pretend we are doing something useful here
    return 13
}

suspend fun doSomethingUsefulTwo(): Int {
    delay(1000L) // pretend we are doing something useful here, too
    return 29
}
```

</div>


What do we do if need to invoke them _sequentially_ -- first `doSomethingUsefulOne` _and then_ 
`doSomethingUsefulTwo` and compute the sum of their results? 
In practice we do this if we use the results of the first function to make a decision on whether we need 
to invoke the second one or to decide on how to invoke it.

We use a normal sequential invocation, because the code in the coroutine, just like in the regular 
code, is _sequential_ by default. The following example demonstrates it by measuring the total 
time it takes to execute both suspending functions:

<!--- CLEAR -->

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

```kotlin
import kotlinx.coroutines.*
import kotlin.system.*

fun main() = runBlocking<Unit> {
//sampleStart
    val time = measureTimeMillis {
        val one = doSomethingUsefulOne()
        val two = doSomethingUsefulTwo()
        println("The answer is ${one + two}")
    }
    println("Completed in $time ms")
//sampleEnd    
}

suspend fun doSomethingUsefulOne(): Int {
    delay(1000L) // pretend we are doing something useful here
    return 13
}

suspend fun doSomethingUsefulTwo(): Int {
    delay(1000L) // pretend we are doing something useful here, too
    return 29
}
```

</div>

> You can get full code [here](../core/kotlinx-coroutines-core/test/guide/example-compose-01.kt)

It produces something like this:

```text
The answer is 42
Completed in 2017 ms
```

<!--- TEST ARBITRARY_TIME -->

### Concurrent using async

What if there are no dependencies between invocation of `doSomethingUsefulOne` and `doSomethingUsefulTwo` and
we want to get the answer faster, by doing both _concurrently_? This is where [async] comes to help. 
 
Conceptually, [async] is just like [launch]. It starts a separate coroutine which is a light-weight thread 
that works concurrently with all the other coroutines. The difference is that `launch` returns a [Job] and 
does not carry any resulting value, while `async` returns a [Deferred] -- a light-weight non-blocking future
that represents a promise to provide a result later. You can use `.await()` on a deferred value to get its eventual result,
but `Deferred` is also a `Job`, so you can cancel it if needed.
 

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">
 
```kotlin
import kotlinx.coroutines.*
import kotlin.system.*

fun main() = runBlocking<Unit> {
//sampleStart
    val time = measureTimeMillis {
        val one = async { doSomethingUsefulOne() }
        val two = async { doSomethingUsefulTwo() }
        println("The answer is ${one.await() + two.await()}")
    }
    println("Completed in $time ms")
//sampleEnd    
}

suspend fun doSomethingUsefulOne(): Int {
    delay(1000L) // pretend we are doing something useful here
    return 13
}

suspend fun doSomethingUsefulTwo(): Int {
    delay(1000L) // pretend we are doing something useful here, too
    return 29
}
```

</div>

> You can get full code [here](../core/kotlinx-coroutines-core/test/guide/example-compose-02.kt)

It produces something like this:

```text
The answer is 42
Completed in 1017 ms
```

<!--- TEST ARBITRARY_TIME -->

This is twice as fast, because we have concurrent execution of two coroutines. 
Note, that concurrency with coroutines is always explicit.

### Lazily started async

There is a laziness option to [async] using an optional `start` parameter with a value of [CoroutineStart.LAZY]. 
It starts coroutine only when its result is needed by some 
[await][Deferred.await] or if a [start][Job.start] function 
is invoked. Run the following example:

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

```kotlin
import kotlinx.coroutines.*
import kotlin.system.*

fun main() = runBlocking<Unit> {
//sampleStart
    val time = measureTimeMillis {
        val one = async(start = CoroutineStart.LAZY) { doSomethingUsefulOne() }
        val two = async(start = CoroutineStart.LAZY) { doSomethingUsefulTwo() }
        // some computation
        one.start() // start the first one
        two.start() // start the second one
        println("The answer is ${one.await() + two.await()}")
    }
    println("Completed in $time ms")
//sampleEnd    
}

suspend fun doSomethingUsefulOne(): Int {
    delay(1000L) // pretend we are doing something useful here
    return 13
}

suspend fun doSomethingUsefulTwo(): Int {
    delay(1000L) // pretend we are doing something useful here, too
    return 29
}
```

</div>

> You can get full code [here](../core/kotlinx-coroutines-core/test/guide/example-compose-03.kt)

It produces something like this:

```text
The answer is 42
Completed in 1017 ms
```

<!--- TEST ARBITRARY_TIME -->

So, here the two coroutines are defined but not executed as in the previous example, but the control is given to
the programmer on when exactly to start the execution by calling [start][Job.start]. We first 
start `one`, then start `two`, and then await for the individual coroutines to finish. 

Note, that if we have called [await][Deferred.await] in `println` and omitted [start][Job.start] on individual 
coroutines, then we would have got the sequential behaviour as [await][Deferred.await] starts the coroutine 
execution and waits for the execution to finish, which is not the intended use-case for laziness. 
The use-case for `async(start = CoroutineStart.LAZY)` is a replacement for the 
standard `lazy` function in cases when computation of the value involves suspending functions.

### Async-style functions

We can define async-style functions that invoke `doSomethingUsefulOne` and `doSomethingUsefulTwo`
_asynchronously_ using [async] coroutine builder with an explicit [GlobalScope] reference.
We name such functions with 
"Async" suffix to highlight the fact that they only start asynchronous computation and one needs
to use the resulting deferred value to get the result.

<div class="sample" markdown="1" theme="idea" data-highlight-only>

```kotlin
// The result type of somethingUsefulOneAsync is Deferred<Int>
fun somethingUsefulOneAsync() = GlobalScope.async {
    doSomethingUsefulOne()
}

// The result type of somethingUsefulTwoAsync is Deferred<Int>
fun somethingUsefulTwoAsync() = GlobalScope.async {
    doSomethingUsefulTwo()
}
```

</div>

Note, that these `xxxAsync` functions are **not** _suspending_ functions. They can be used from anywhere.
However, their use always implies asynchronous (here meaning _concurrent_) execution of their action
with the invoking code.
 
The following example shows their use outside of coroutine:  

<!--- CLEAR -->

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">
 
```kotlin
import kotlinx.coroutines.*
import kotlin.system.*

//sampleStart
// note, that we don't have `runBlocking` to the right of `main` in this example
fun main() {
    val time = measureTimeMillis {
        // we can initiate async actions outside of a coroutine
        val one = somethingUsefulOneAsync()
        val two = somethingUsefulTwoAsync()
        // but waiting for a result must involve either suspending or blocking.
        // here we use `runBlocking { ... }` to block the main thread while waiting for the result
        runBlocking {
            println("The answer is ${one.await() + two.await()}")
        }
    }
    println("Completed in $time ms")
}
//sampleEnd

fun somethingUsefulOneAsync() = GlobalScope.async {
    doSomethingUsefulOne()
}

fun somethingUsefulTwoAsync() = GlobalScope.async {
    doSomethingUsefulTwo()
}

suspend fun doSomethingUsefulOne(): Int {
    delay(1000L) // pretend we are doing something useful here
    return 13
}

suspend fun doSomethingUsefulTwo(): Int {
    delay(1000L) // pretend we are doing something useful here, too
    return 29
}
```

</div>

> You can get full code [here](../core/kotlinx-coroutines-core/test/guide/example-compose-04.kt)

<!--- TEST ARBITRARY_TIME
The answer is 42
Completed in 1085 ms
-->

> This programming style with async functions is provided here only for illustration, because it is a popular style
in other programming languages. Using this style with Kotlin coroutines is **strongly discouraged** for the
reasons that are explained below.

Consider what happens if between `val one = somethingUsefulOneAsync()` line and `one.await()` expression there is some logic
error in the code and the program throws an exception and the operation that was being performed by the program aborts. 
Normally, a global error-handler could catch this exception, log and report the error for developers, but the program 
could otherwise continue doing other operations. But here we have `somethingUsefulOneAsync` still running in background,
despite the fact, that operation that had initiated it aborts. This problem does not happen with structured
concurrency, as shown in the section below.

### Structured concurrency with async 

Let us take [Concurrent using async](#concurrent-using-async) example and extract a function that 
concurrently performs `doSomethingUsefulOne` and `doSomethingUsefulTwo` and returns the sum of their results.
Because [async] coroutines builder is defined as extension on [CoroutineScope] we need to have it in the 
scope and that is what [coroutineScope] function provides:

<div class="sample" markdown="1" theme="idea" data-highlight-only>

```kotlin
suspend fun concurrentSum(): Int = coroutineScope {
    val one = async { doSomethingUsefulOne() }
    val two = async { doSomethingUsefulTwo() }
    one.await() + two.await()
}
```

</div>

This way, if something goes wrong inside the code of `concurrentSum` function and it throws an exception,
all the coroutines that were launched in its scope are cancelled.

<!--- CLEAR -->

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">
 
```kotlin
import kotlinx.coroutines.*
import kotlin.system.*

fun main() = runBlocking<Unit> {
    //sampleStart
    val time = measureTimeMillis {
        println("The answer is ${concurrentSum()}")
    }
    println("Completed in $time ms")
    //sampleEnd    
}

suspend fun concurrentSum(): Int = coroutineScope {
    val one = async { doSomethingUsefulOne() }
    val two = async { doSomethingUsefulTwo() }
    one.await() + two.await()
}

suspend fun doSomethingUsefulOne(): Int {
    delay(1000L) // pretend we are doing something useful here
    return 13
}

suspend fun doSomethingUsefulTwo(): Int {
    delay(1000L) // pretend we are doing something useful here, too
    return 29
}
```

</div>

> You can get full code [here](../core/kotlinx-coroutines-core/test/guide/example-compose-05.kt)

We still have concurrent execution of both operations as evident from the output of the above main function: 

```text
The answer is 42
Completed in 1017 ms
```

<!--- TEST ARBITRARY_TIME -->

Cancellation is always propagated through coroutines hierarchy:

<!--- CLEAR -->

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

```kotlin
import kotlinx.coroutines.*

fun main() = runBlocking<Unit> {
    try {
        failedConcurrentSum()
    } catch(e: ArithmeticException) {
        println("Computation failed with ArithmeticException")
    }
}

suspend fun failedConcurrentSum(): Int = coroutineScope {
    val one = async<Int> { 
        try {
            delay(Long.MAX_VALUE) // Emulates very long computation
            42
        } finally {
            println("First child was cancelled")
        }
    }
    val two = async<Int> { 
        println("Second child throws an exception")
        throw ArithmeticException()
    }
    one.await() + two.await()
}
```

</div>

> You can get full code [here](../core/kotlinx-coroutines-core/test/guide/example-compose-06.kt)

Note, how both first `async` and awaiting parent are cancelled on the one child failure:
```text
Second child throws an exception
First child was cancelled
Computation failed with ArithmeticException
```

<!--- TEST -->

<!--- MODULE kotlinx-coroutines-core -->
<!--- INDEX kotlinx.coroutines -->
[async]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/async.html
[launch]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/launch.html
[Job]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-job/index.html
[Deferred]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-deferred/index.html
[CoroutineStart.LAZY]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-coroutine-start/-l-a-z-y.html
[Deferred.await]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-deferred/await.html
[Job.start]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-job/start.html
[GlobalScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-global-scope/index.html
[CoroutineScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-coroutine-scope/index.html
[coroutineScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/coroutine-scope.html
<!--- END -->
