<!--- TEST_NAME ComposingGuideTest -->

[//]: # (title: Composing suspending functions)

This section covers various approaches to composition of suspending functions.

## Sequential by default

Assume that we have two suspending functions defined elsewhere that do something useful like some kind of 
remote service call or computation. We just pretend they are useful, but actually each one just
delays for a second for the purpose of this example:

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

What do we do if we need them to be invoked _sequentially_ &mdash; first `doSomethingUsefulOne` _and then_ 
`doSomethingUsefulTwo`, and compute the sum of their results? 
In practice we do this if we use the result of the first function to make a decision on whether we need 
to invoke the second one or to decide on how to invoke it.

We use a normal sequential invocation, because the code in the coroutine, just like in the regular 
code, is _sequential_ by default. The following example demonstrates it by measuring the total 
time it takes to execute both suspending functions:

<!--- CLEAR -->

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
{kotlin-runnable="true" kotlin-min-compiler-version="1.3"}

> You can get the full code [here](../../kotlinx-coroutines-core/jvm/test/guide/example-compose-01.kt).
>
{type="note"}

It produces something like this:

```text
The answer is 42
Completed in 2017 ms
```

<!--- TEST ARBITRARY_TIME -->

## Concurrent using async

What if there are no dependencies between invocations of `doSomethingUsefulOne` and `doSomethingUsefulTwo` and
we want to get the answer faster, by doing both _concurrently_? This is where [async] comes to help. 
 
Conceptually, [async] is just like [launch]. It starts a separate coroutine which is a light-weight thread 
that works concurrently with all the other coroutines. The difference is that `launch` returns a [Job] and 
does not carry any resulting value, while `async` returns a [Deferred] &mdash; a light-weight non-blocking future
that represents a promise to provide a result later. You can use `.await()` on a deferred value to get its eventual result,
but `Deferred` is also a `Job`, so you can cancel it if needed.

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
{kotlin-runnable="true" kotlin-min-compiler-version="1.3"}

> You can get the full code [here](../../kotlinx-coroutines-core/jvm/test/guide/example-compose-02.kt).
>
{type="note"}

It produces something like this:

```text
The answer is 42
Completed in 1017 ms
```

<!--- TEST ARBITRARY_TIME -->

This is twice as fast, because the two coroutines execute concurrently. 
Note that concurrency with coroutines is always explicit.

## Lazily started async

Optionally, [async] can be made lazy by setting its `start` parameter to [CoroutineStart.LAZY]. 
In this mode it only starts the coroutine when its result is required by 
[await][Deferred.await], or if its `Job`'s [start][Job.start] function 
is invoked. Run the following example:

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
{kotlin-runnable="true" kotlin-min-compiler-version="1.3"}

> You can get the full code [here](../../kotlinx-coroutines-core/jvm/test/guide/example-compose-03.kt).
>
{type="note"}

It produces something like this:

```text
The answer is 42
Completed in 1017 ms
```

<!--- TEST ARBITRARY_TIME -->

So, here the two coroutines are defined but not executed as in the previous example, but the control is given to
the programmer on when exactly to start the execution by calling [start][Job.start]. We first 
start `one`, then start `two`, and then await for the individual coroutines to finish. 

Note that if we just call [await][Deferred.await] in `println` without first calling [start][Job.start] on individual 
coroutines, this will lead to sequential behavior, since [await][Deferred.await] starts the coroutine 
execution and waits for its finish, which is not the intended use-case for laziness. 
The use-case for `async(start = CoroutineStart.LAZY)` is a replacement for the 
standard `lazy` function in cases when computation of the value involves suspending functions.

## Async-style functions

We can define async-style functions that invoke `doSomethingUsefulOne` and `doSomethingUsefulTwo`
_asynchronously_ using the [async] coroutine builder with an explicit [GlobalScope] reference.
We name such functions with the 
"...Async" suffix to highlight the fact that they only start asynchronous computation and one needs
to use the resulting deferred value to get the result.

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

Note that these `xxxAsync` functions are **not** _suspending_ functions. They can be used from anywhere.
However, their use always implies asynchronous (here meaning _concurrent_) execution of their action
with the invoking code.
 
The following example shows their use outside of coroutine:

<!--- CLEAR -->

```kotlin
import kotlinx.coroutines.*
import kotlin.system.*

//sampleStart
// note that we don't have `runBlocking` to the right of `main` in this example
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
{kotlin-runnable="true" kotlin-min-compiler-version="1.3"}

> You can get the full code [here](../../kotlinx-coroutines-core/jvm/test/guide/example-compose-04.kt).
>
{type="note"}

<!--- TEST ARBITRARY_TIME
The answer is 42
Completed in 1085 ms
-->

> This programming style with async functions is provided here only for illustration, because it is a popular style
> in other programming languages. Using this style with Kotlin coroutines is **strongly discouraged** for the
> reasons explained below.
>
{type="note"}

Consider what happens if between the `val one = somethingUsefulOneAsync()` line and `one.await()` expression there is some logic
error in the code and the program throws an exception and the operation that was being performed by the program aborts. 
Normally, a global error-handler could catch this exception, log and report the error for developers, but the program 
could otherwise continue doing other operations. But here we have `somethingUsefulOneAsync` still running in the background,
even though the operation that initiated it was aborted. This problem does not happen with structured
concurrency, as shown in the section below.

## Structured concurrency with async 

Let us take the [Concurrent using async](#concurrent-using-async) example and extract a function that 
concurrently performs `doSomethingUsefulOne` and `doSomethingUsefulTwo` and returns the sum of their results.
Because the [async] coroutine builder is defined as an extension on [CoroutineScope], we need to have it in the 
scope and that is what the [coroutineScope][_coroutineScope] function provides:

```kotlin
suspend fun concurrentSum(): Int = coroutineScope {
    val one = async { doSomethingUsefulOne() }
    val two = async { doSomethingUsefulTwo() }
    one.await() + two.await()
}
```

This way, if something goes wrong inside the code of the `concurrentSum` function and it throws an exception,
all the coroutines that were launched in its scope will be cancelled.

<!--- CLEAR -->

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
{kotlin-runnable="true" kotlin-min-compiler-version="1.3"}

> You can get the full code [here](../../kotlinx-coroutines-core/jvm/test/guide/example-compose-05.kt).
>
{type="note"}

We still have concurrent execution of both operations, as evident from the output of the above `main` function: 

```text
The answer is 42
Completed in 1017 ms
```

<!--- TEST ARBITRARY_TIME -->

Cancellation is always propagated through coroutines hierarchy:

<!--- CLEAR -->

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
{kotlin-runnable="true" kotlin-min-compiler-version="1.3"}

> You can get the full code [here](../../kotlinx-coroutines-core/jvm/test/guide/example-compose-06.kt).
>
{type="note"}

Note how both the first `async` and the awaiting parent are cancelled on failure of one of the children
(namely, `two`):
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
[_coroutineScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/coroutine-scope.html

<!--- END -->