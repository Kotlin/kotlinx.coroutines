<!--- INCLUDE .*/example-([a-z]+)-([0-9a-z]+)\.kt 
/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

// This file was automatically generated from coroutines-guide.md by Knit tool. Do not edit.
package kotlinx.coroutines.guide.$$1$$2
-->
<!--- KNIT     ../core/kotlinx-coroutines-core/test/guide/.*\.kt -->
<!--- TEST_OUT ../core/kotlinx-coroutines-core/test/guide/test/CancellationTimeOutsGuideTest.kt
// This file was automatically generated from coroutines-guide.md by Knit tool. Do not edit.
package kotlinx.coroutines.guide.test

import org.junit.Test

class CancellationTimeOutsGuideTest {
--> 
**Table of contents**

<!--- TOC -->

* [Cancellation and timeouts](#cancellation-and-timeouts)
  * [Cancelling coroutine execution](#cancelling-coroutine-execution)
  * [Cancellation is cooperative](#cancellation-is-cooperative)
  * [Making computation code cancellable](#making-computation-code-cancellable)
  * [Closing resources with finally](#closing-resources-with-finally)
  * [Run non-cancellable block](#run-non-cancellable-block)
  * [Timeout](#timeout)

<!--- END_TOC -->

## Cancellation and timeouts

This section covers coroutine cancellation and timeouts.

### Cancelling coroutine execution

In a long-running application you might need fine-grained control on your background coroutines.
For example, a user might have closed the page that launched a coroutine and now its result
is no longer needed and its operation can be cancelled. 
The [launch] function returns a [Job] that can be used to cancel running coroutine:
 
<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">
 
```kotlin
import kotlinx.coroutines.*

fun main() = runBlocking {
//sampleStart
    val job = launch {
        repeat(1000) { i ->
            println("I'm sleeping $i ...")
            delay(500L)
        }
    }
    delay(1300L) // delay a bit
    println("main: I'm tired of waiting!")
    job.cancel() // cancels the job
    job.join() // waits for job's completion 
    println("main: Now I can quit.")
//sampleEnd    
}
``` 

</div>

> You can get full code [here](../core/kotlinx-coroutines-core/test/guide/example-cancel-01.kt)

It produces the following output:

```text
I'm sleeping 0 ...
I'm sleeping 1 ...
I'm sleeping 2 ...
main: I'm tired of waiting!
main: Now I can quit.
```

<!--- TEST -->

As soon as main invokes `job.cancel`, we don't see any output from the other coroutine because it was cancelled. 
There is also a [Job] extension function [cancelAndJoin] 
that combines [cancel][Job.cancel] and [join][Job.join] invocations.

### Cancellation is cooperative

Coroutine cancellation is _cooperative_. A coroutine code has to cooperate to be cancellable.
All the suspending functions in `kotlinx.coroutines` are _cancellable_. They check for cancellation of 
coroutine and throw [CancellationException] when cancelled. However, if a coroutine is working in 
a computation and does not check for cancellation, then it cannot be cancelled, like the following 
example shows:

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

```kotlin
import kotlinx.coroutines.*

fun main() = runBlocking {
//sampleStart
    val startTime = System.currentTimeMillis()
    val job = launch(Dispatchers.Default) {
        var nextPrintTime = startTime
        var i = 0
        while (i < 5) { // computation loop, just wastes CPU
            // print a message twice a second
            if (System.currentTimeMillis() >= nextPrintTime) {
                println("I'm sleeping ${i++} ...")
                nextPrintTime += 500L
            }
        }
    }
    delay(1300L) // delay a bit
    println("main: I'm tired of waiting!")
    job.cancelAndJoin() // cancels the job and waits for its completion
    println("main: Now I can quit.")
//sampleEnd    
}
```

</div>

> You can get full code [here](../core/kotlinx-coroutines-core/test/guide/example-cancel-02.kt)

Run it to see that it continues to print "I'm sleeping" even after cancellation
until the job completes by itself after five iterations.

<!--- TEST 
I'm sleeping 0 ...
I'm sleeping 1 ...
I'm sleeping 2 ...
main: I'm tired of waiting!
I'm sleeping 3 ...
I'm sleeping 4 ...
main: Now I can quit.
-->

### Making computation code cancellable

There are two approaches to making computation code cancellable. The first one is to periodically 
invoke a suspending function that checks for cancellation. There is a [yield] function that is a good choice for that purpose.
The other one is to explicitly check the cancellation status. Let us try the latter approach. 

Replace `while (i < 5)` in the previous example with `while (isActive)` and rerun it. 

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

```kotlin
import kotlinx.coroutines.*

fun main() = runBlocking {
//sampleStart
    val startTime = System.currentTimeMillis()
    val job = launch(Dispatchers.Default) {
        var nextPrintTime = startTime
        var i = 0
        while (isActive) { // cancellable computation loop
            // print a message twice a second
            if (System.currentTimeMillis() >= nextPrintTime) {
                println("I'm sleeping ${i++} ...")
                nextPrintTime += 500L
            }
        }
    }
    delay(1300L) // delay a bit
    println("main: I'm tired of waiting!")
    job.cancelAndJoin() // cancels the job and waits for its completion
    println("main: Now I can quit.")
//sampleEnd    
}
```

</div>

> You can get full code [here](../core/kotlinx-coroutines-core/test/guide/example-cancel-03.kt)

As you can see, now this loop is cancelled. [isActive] is an extension property that is
available inside the code of coroutine via [CoroutineScope] object.

<!--- TEST
I'm sleeping 0 ...
I'm sleeping 1 ...
I'm sleeping 2 ...
main: I'm tired of waiting!
main: Now I can quit.
-->

### Closing resources with finally

Cancellable suspending functions throw [CancellationException] on cancellation which can be handled in 
a usual way. For example, `try {...} finally {...}` expression and Kotlin `use` function execute their
finalization actions normally when coroutine is cancelled:
 
 
<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">
 
```kotlin
import kotlinx.coroutines.*

fun main() = runBlocking {
//sampleStart
    val job = launch {
        try {
            repeat(1000) { i ->
                println("I'm sleeping $i ...")
                delay(500L)
            }
        } finally {
            println("I'm running finally")
        }
    }
    delay(1300L) // delay a bit
    println("main: I'm tired of waiting!")
    job.cancelAndJoin() // cancels the job and waits for its completion
    println("main: Now I can quit.")
//sampleEnd    
}
``` 

</div>

> You can get full code [here](../core/kotlinx-coroutines-core/test/guide/example-cancel-04.kt)

Both [join][Job.join] and [cancelAndJoin] wait for all the finalization actions to complete, 
so the example above produces the following output:

```text
I'm sleeping 0 ...
I'm sleeping 1 ...
I'm sleeping 2 ...
main: I'm tired of waiting!
I'm running finally
main: Now I can quit.
```

<!--- TEST -->

### Run non-cancellable block

Any attempt to use a suspending function in the `finally` block of the previous example causes
[CancellationException], because the coroutine running this code is cancelled. Usually, this is not a 
problem, since all well-behaving closing operations (closing a file, cancelling a job, or closing any kind of a 
communication channel) are usually non-blocking and do not involve any suspending functions. However, in the 
rare case when you need to suspend in the cancelled coroutine you can wrap the corresponding code in
`withContext(NonCancellable) {...}` using [withContext] function and [NonCancellable] context as the following example shows:
 
<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">
 
```kotlin
import kotlinx.coroutines.*

fun main() = runBlocking {
//sampleStart
    val job = launch {
        try {
            repeat(1000) { i ->
                println("I'm sleeping $i ...")
                delay(500L)
            }
        } finally {
            withContext(NonCancellable) {
                println("I'm running finally")
                delay(1000L)
                println("And I've just delayed for 1 sec because I'm non-cancellable")
            }
        }
    }
    delay(1300L) // delay a bit
    println("main: I'm tired of waiting!")
    job.cancelAndJoin() // cancels the job and waits for its completion
    println("main: Now I can quit.")
//sampleEnd    
}
``` 

</div>

> You can get full code [here](../core/kotlinx-coroutines-core/test/guide/example-cancel-05.kt)

<!--- TEST
I'm sleeping 0 ...
I'm sleeping 1 ...
I'm sleeping 2 ...
main: I'm tired of waiting!
I'm running finally
And I've just delayed for 1 sec because I'm non-cancellable
main: Now I can quit.
-->

### Timeout

The most obvious reason to cancel coroutine execution in practice 
is because its execution time has exceeded some timeout.
While you can manually track the reference to the corresponding [Job] and launch a separate coroutine to cancel 
the tracked one after delay, there is a ready to use [withTimeout] function that does it.
Look at the following example:

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

```kotlin
import kotlinx.coroutines.*

fun main() = runBlocking {
//sampleStart
    withTimeout(1300L) {
        repeat(1000) { i ->
            println("I'm sleeping $i ...")
            delay(500L)
        }
    }
//sampleEnd
}
```

</div>

> You can get full code [here](../core/kotlinx-coroutines-core/test/guide/example-cancel-06.kt)

It produces the following output:

```text
I'm sleeping 0 ...
I'm sleeping 1 ...
I'm sleeping 2 ...
Exception in thread "main" kotlinx.coroutines.TimeoutCancellationException: Timed out waiting for 1300 ms
```

<!--- TEST STARTS_WITH -->

The `TimeoutCancellationException` that is thrown by [withTimeout] is a subclass of [CancellationException].
We have not seen its stack trace printed on the console before. That is because
inside a cancelled coroutine `CancellationException` is considered to be a normal reason for coroutine completion. 
However, in this example we have used `withTimeout` right inside the `main` function. 

Because cancellation is just an exception, all the resources are closed in a usual way. 
You can wrap the code with timeout in `try {...} catch (e: TimeoutCancellationException) {...}` block if 
you need to do some additional action specifically on any kind of timeout or use [withTimeoutOrNull] function
that is similar to [withTimeout], but returns `null` on timeout instead of throwing an exception:

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

```kotlin
import kotlinx.coroutines.*

fun main() = runBlocking {
//sampleStart
    val result = withTimeoutOrNull(1300L) {
        repeat(1000) { i ->
            println("I'm sleeping $i ...")
            delay(500L)
        }
        "Done" // will get cancelled before it produces this result
    }
    println("Result is $result")
//sampleEnd
}
```

</div>

> You can get full code [here](../core/kotlinx-coroutines-core/test/guide/example-cancel-07.kt)

There is no longer an exception when running this code:

```text
I'm sleeping 0 ...
I'm sleeping 1 ...
I'm sleeping 2 ...
Result is null
```

<!--- TEST -->

<!--- MODULE kotlinx-coroutines-core -->
<!--- INDEX kotlinx.coroutines -->
[launch]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/launch.html
[Job]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-job/index.html
[cancelAndJoin]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/cancel-and-join.html
[Job.cancel]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-job/cancel.html
[Job.join]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-job/join.html
[CancellationException]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-cancellation-exception/index.html
[yield]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/yield.html
[isActive]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/is-active.html
[CoroutineScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-coroutine-scope/index.html
[withContext]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/with-context.html
[NonCancellable]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-non-cancellable.html
[withTimeout]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/with-timeout.html
[withTimeoutOrNull]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/with-timeout-or-null.html
<!--- END -->
