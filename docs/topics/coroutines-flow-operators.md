<!--- TEST_NAME FlowGuideTest --> 
<contribute-url>https://github.com/Kotlin/kotlinx.coroutines/edit/master/docs/topics/</contribute-url>

[//]: # (title: Flow operators)

> This page is currently being revised. For up-to-date Flow guidance, start with the [Flow overview](coroutines-flow.md).
>
{style="note"}

Flows can be transformed using operators, in the same way as you would transform collections and
sequences.
Intermediate operators are applied to an upstream flow and return a downstream flow.
These operators are cold. A call to such an operator is not
a suspending function itself. It works quickly, returning the definition of a new transformed flow.

The basic operators have familiar names like [map] and [filter].
An important difference of these operators from sequences is that blocks of
code inside these operators can call suspending functions.

For example, a flow of incoming requests can be
mapped to its results with a [map] operator, even when performing a request is a long-running
operation that is implemented by a suspending function:

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*

//sampleStart           
suspend fun performRequest(request: Int): String {
    delay(1000) // imitate long-running asynchronous work
    return "response $request"
}

fun main() = runBlocking<Unit> {
    (1..3).asFlow() // a flow of requests
        .map { request -> performRequest(request) }
        .collect { response -> println(response) }
}
//sampleEnd
```
{kotlin-runnable="true" kotlin-min-compiler-version="1.3"}
<!--- KNIT example-flow-01.kt -->
> You can get the full code [here](https://github.com/Kotlin/kotlinx.coroutines/blob/master/kotlinx-coroutines-core/jvm/test/guide/example-flow-08.kt).
>
{style="note"}

It produces the following three lines, each appearing one second after the previous:

```text                                                                    
response 1
response 2
response 3
```

<!--- TEST -->

### Transform operator

Among the flow transformation operators, the most general one is called [transform]. It can be used to imitate
simple transformations like [map] and [filter], as well as implement more complex transformations.
Using the `transform` operator, we can [emit][FlowCollector.emit] arbitrary values an arbitrary number of times.

For example, using `transform` we can emit a string before performing a long-running asynchronous request
and follow it with a response:

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*

suspend fun performRequest(request: Int): String {
    delay(1000) // imitate long-running asynchronous work
    return "response $request"
}

fun main() = runBlocking<Unit> {
//sampleStart
    (1..3).asFlow() // a flow of requests
        .transform { request ->
            emit("Making request $request") 
            emit(performRequest(request)) 
        }
        .collect { response -> println(response) }
//sampleEnd
}
```
{kotlin-runnable="true" kotlin-min-compiler-version="1.3"}
<!--- KNIT example-flow-02.kt -->
> You can get the full code [here](https://github.com/Kotlin/kotlinx.coroutines/blob/master/kotlinx-coroutines-core/jvm/test/guide/example-flow-09.kt).
>
{style="note"}

The output of this code is:

```text
Making request 1
response 1
Making request 2
response 2
Making request 3
response 3
```

<!--- TEST -->

### Size-limiting operators

Size-limiting intermediate operators like [take] cancel the execution of the flow when the corresponding limit
is reached. Cancellation in coroutines is always performed by throwing an exception, so that all the resource-management
functions (like `try { ... } finally { ... }` blocks) operate normally in case of cancellation:

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*

//sampleStart
fun numbers(): Flow<Int> = flow {
    try {                          
        emit(1)
        emit(2) 
        println("This line will not execute")
        emit(3)    
    } finally {
        println("Finally in numbers")
    }
}

fun main() = runBlocking<Unit> {
    numbers() 
        .take(2) // take only the first two
        .collect { value -> println(value) }
}            
//sampleEnd
```
{kotlin-runnable="true" kotlin-min-compiler-version="1.3"}
<!--- KNIT example-flow-03.kt -->
> You can get the full code [here](https://github.com/Kotlin/kotlinx.coroutines/blob/master/kotlinx-coroutines-core/jvm/test/guide/example-flow-10.kt).
>
{style="note"}

The output of this code clearly shows that the execution of the `flow { ... }` body in the `numbers()` function
stopped after emitting the second number:

```text       
1
2
Finally in numbers
```

<!--- TEST -->

## Terminal flow operators

Terminal operators on flows are _suspending functions_ that start a collection of the flow.
The [collect] operator is the most basic one, but there are other terminal operators, which can make it easier:

* Conversion to various collections like [toList] and [toSet].
* Operators to get the [first] value and to ensure that a flow emits a [single] value.
* Reducing a flow to a value with [reduce] and [fold].

For example:

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*

fun main() = runBlocking<Unit> {
//sampleStart         
    val sum = (1..5).asFlow()
        .map { it * it } // squares of numbers from 1 to 5                           
        .reduce { a, b -> a + b } // sum them (terminal operator)
    println(sum)
//sampleEnd     
}
```
{kotlin-runnable="true" kotlin-min-compiler-version="1.3"}
<!--- KNIT example-flow-04.kt -->
> You can get the full code [here](https://github.com/Kotlin/kotlinx.coroutines/blob/master/kotlinx-coroutines-core/jvm/test/guide/example-flow-11.kt).
>
{style="note"}

Prints a single number:

```text
55
```

<!--- TEST -->

## Buffering

Running different parts of a flow in different coroutines can be helpful from the standpoint of the overall time it takes
to collect the flow, especially when long-running asynchronous operations are involved. For example, consider a case when
the emission by a `simple` flow is slow, taking 100 ms to produce an element; and collector is also slow,
taking 300 ms to process an element. Let's see how long it takes to collect such a flow with three numbers:

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlin.system.*

//sampleStart
fun simple(): Flow<Int> = flow {
    for (i in 1..3) {
        delay(100) // pretend we are asynchronously waiting 100 ms
        emit(i) // emit next value
    }
}

fun main() = runBlocking<Unit> { 
    val time = measureTimeMillis {
        simple().collect { value -> 
            delay(300) // pretend we are processing it for 300 ms
            println(value) 
        } 
    }   
    println("Collected in $time ms")
}
//sampleEnd
```
{kotlin-runnable="true" kotlin-min-compiler-version="1.3"}
<!--- KNIT example-flow-05.kt -->
> You can get the full code [here](https://github.com/Kotlin/kotlinx.coroutines/blob/master/kotlinx-coroutines-core/jvm/test/guide/example-flow-16.kt).
>
{style="note"}

It produces something like this, with the whole collection taking around 1200 ms (three numbers, 400 ms for each):

```text
1
2
3
Collected in 1220 ms
```

<!--- TEST ARBITRARY_TIME -->

We can use a [buffer] operator on a flow to run emitting code of the `simple` flow concurrently with collecting code,
as opposed to running them sequentially:

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlin.system.*

fun simple(): Flow<Int> = flow {
    for (i in 1..3) {
        delay(100) // pretend we are asynchronously waiting 100 ms
        emit(i) // emit next value
    }
}

fun main() = runBlocking<Unit> { 
//sampleStart
    val time = measureTimeMillis {
        simple()
            .buffer() // buffer emissions, don't wait
            .collect { value -> 
                delay(300) // pretend we are processing it for 300 ms
                println(value) 
            } 
    }   
    println("Collected in $time ms")
//sampleEnd
}
```
{kotlin-runnable="true" kotlin-min-compiler-version="1.3"}
<!--- KNIT example-flow-06.kt -->
> You can get the full code [here](https://github.com/Kotlin/kotlinx.coroutines/blob/master/kotlinx-coroutines-core/jvm/test/guide/example-flow-17.kt).
>
{style="note"}

It produces the same numbers just faster, as we have effectively created a processing pipeline,
having to only wait 100 ms for the first number and then spending only 300 ms to process
each number. This way it takes around 1000 ms to run:

```text
1
2
3
Collected in 1071 ms
```                    

<!--- TEST ARBITRARY_TIME -->

> Note that the [flowOn] operator uses the same buffering mechanism when it has to change a [CoroutineDispatcher],
> but here we explicitly request buffering without changing the execution context.
>
{style="note"}

### Conflation

When a flow represents partial results of the operation or operation status updates, it may not be necessary
to process each value, but instead, only most recent ones. In this case, the [conflate] operator can be used to skip
intermediate values when a collector is too slow to process them. Building on the previous example:

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlin.system.*

fun simple(): Flow<Int> = flow {
    for (i in 1..3) {
        delay(100) // pretend we are asynchronously waiting 100 ms
        emit(i) // emit next value
    }
}

fun main() = runBlocking<Unit> { 
//sampleStart
    val time = measureTimeMillis {
        simple()
            .conflate() // conflate emissions, don't process each one
            .collect { value -> 
                delay(300) // pretend we are processing it for 300 ms
                println(value) 
            } 
    }   
    println("Collected in $time ms")
//sampleEnd
}
```
{kotlin-runnable="true" kotlin-min-compiler-version="1.3"}
<!--- KNIT example-flow-07.kt -->
> You can get the full code [here](https://github.com/Kotlin/kotlinx.coroutines/blob/master/kotlinx-coroutines-core/jvm/test/guide/example-flow-18.kt).
>
{style="note"}

We see that while the first number was still being processed the second, and third were already produced, so
the second one was _conflated_ and only the most recent (the third one) was delivered to the collector:

```text
1
3
Collected in 758 ms
```             

<!--- TEST ARBITRARY_TIME -->

### Processing the latest value

Conflation is one way to speed up processing when both the emitter and collector are slow. It does it by dropping emitted values.
The other way is to cancel a slow collector and restart it every time a new value is emitted. There is
a family of `xxxLatest` operators that perform the same essential logic of a `xxx` operator, but cancel the
code in their block on a new value. Let's try changing [conflate] to [collectLatest] in the previous example:

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlin.system.*

fun simple(): Flow<Int> = flow {
    for (i in 1..3) {
        delay(100) // pretend we are asynchronously waiting 100 ms
        emit(i) // emit next value
    }
}

fun main() = runBlocking<Unit> { 
//sampleStart
    val time = measureTimeMillis {
        simple()
            .collectLatest { value -> // cancel & restart on the latest value
                println("Collecting $value") 
                delay(300) // pretend we are processing it for 300 ms
                println("Done $value") 
            } 
    }   
    println("Collected in $time ms")
//sampleEnd
}
```
{kotlin-runnable="true" kotlin-min-compiler-version="1.3"}
<!--- KNIT example-flow-08.kt -->
> You can get the full code [here](https://github.com/Kotlin/kotlinx.coroutines/blob/master/kotlinx-coroutines-core/jvm/test/guide/example-flow-19.kt).
>
{style="note"}

Since the body of [collectLatest] takes 300 ms, but new values are emitted every 100 ms, we see that the block
is run on every value, but completes only for the last value:

```text 
Collecting 1
Collecting 2
Collecting 3
Done 3
Collected in 741 ms
``` 

<!--- TEST ARBITRARY_TIME -->

## Composing multiple flows

There are lots of ways to compose multiple flows.

### Zip

Just like the [Sequence.zip] extension function in the Kotlin standard library,
flows have a [zip] operator that combines the corresponding values of two flows:

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*

fun main() = runBlocking<Unit> { 
//sampleStart                                                                           
    val nums = (1..3).asFlow() // numbers 1..3
    val strs = flowOf("one", "two", "three") // strings 
    nums.zip(strs) { a, b -> "$a -> $b" } // compose a single string
        .collect { println(it) } // collect and print
//sampleEnd
}
```
{kotlin-runnable="true" kotlin-min-compiler-version="1.3"}
<!--- KNIT example-flow-09.kt -->
> You can get the full code [here](https://github.com/Kotlin/kotlinx.coroutines/blob/master/kotlinx-coroutines-core/jvm/test/guide/example-flow-20.kt).
>
{style="note"}

This example prints:

```text
1 -> one
2 -> two
3 -> three
```

<!--- TEST -->

### Combine

When flow represents the most recent value of a variable or operation (see also the related
section on [conflation](#conflation)), it might be needed to perform a computation that depends on
the most recent values of the corresponding flows and to recompute it whenever any of the upstream
flows emit a value. The corresponding family of operators is called [combine].

For example, if the numbers in the previous example update every 300ms, but strings update every 400 ms,
then zipping them using the [zip] operator will still produce the same result,
albeit results that are printed every 400 ms:

> We use a [onEach] intermediate operator in this example to delay each element and make the code
> that emits sample flows more declarative and shorter.
>
{style="note"}

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*

fun main() = runBlocking<Unit> { 
//sampleStart                                                                           
    val nums = (1..3).asFlow().onEach { delay(300) } // numbers 1..3 every 300 ms
    val strs = flowOf("one", "two", "three").onEach { delay(400) } // strings every 400 ms
    val startTime = System.currentTimeMillis() // remember the start time 
    nums.zip(strs) { a, b -> "$a -> $b" } // compose a single string with "zip"
        .collect { value -> // collect and print 
            println("$value at ${System.currentTimeMillis() - startTime} ms from start") 
        } 
//sampleEnd
}
```
{kotlin-runnable="true" kotlin-min-compiler-version="1.3"}
<!--- KNIT example-flow-10.kt -->
> You can get the full code [here](https://github.com/Kotlin/kotlinx.coroutines/blob/master/kotlinx-coroutines-core/jvm/test/guide/example-flow-21.kt).
>
{style="note"}

<!--- TEST ARBITRARY_TIME
1 -> one at 437 ms from start
2 -> two at 837 ms from start
3 -> three at 1243 ms from start
-->

However, when using a [combine] operator here instead of a [zip]:

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*

fun main() = runBlocking<Unit> { 
//sampleStart                                                                           
    val nums = (1..3).asFlow().onEach { delay(300) } // numbers 1..3 every 300 ms
    val strs = flowOf("one", "two", "three").onEach { delay(400) } // strings every 400 ms          
    val startTime = System.currentTimeMillis() // remember the start time 
    nums.combine(strs) { a, b -> "$a -> $b" } // compose a single string with "combine"
        .collect { value -> // collect and print 
            println("$value at ${System.currentTimeMillis() - startTime} ms from start") 
        } 
//sampleEnd
}
```
{kotlin-runnable="true" kotlin-min-compiler-version="1.3"}
<!--- KNIT example-flow-11.kt -->
> You can get the full code [here](https://github.com/Kotlin/kotlinx.coroutines/blob/master/kotlinx-coroutines-core/jvm/test/guide/example-flow-22.kt).
>
{style="note"}

We get quite a different output, where a line is printed at each emission from either `nums` or `strs` flows:

```text 
1 -> one at 452 ms from start
2 -> one at 651 ms from start
2 -> two at 854 ms from start
3 -> two at 952 ms from start
3 -> three at 1256 ms from start
```

<!--- TEST ARBITRARY_TIME -->

## Flattening flows

Flows represent asynchronously received sequences of values, and so it is quite easy to get into a situation
where each value triggers a request for another sequence of values. For example, we can have the following
function that returns a flow of two strings 500 ms apart:

```kotlin
fun requestFlow(i: Int): Flow<String> = flow {
    emit("$i: First") 
    delay(500) // wait 500 ms
    emit("$i: Second")    
}
```

<!--- CLEAR -->

Now if we have a flow of three integers and call `requestFlow` on each of them like this:

```kotlin
(1..3).asFlow().map { requestFlow(it) }
```

<!--- CLEAR -->

Then we will end up with a flow of flows (`Flow<Flow<String>>`) that needs to be _flattened_ into a single flow for
further processing. Collections and sequences have [flatten][Sequence.flatten] and [flatMap][Sequence.flatMap]
operators for this. However, due to the asynchronous nature of flows they call for different _modes_ of flattening,
and hence, a family of flattening operators on flows exists.

### flatMapConcat

Concatenation of flows of flows is provided by the [flatMapConcat] and [flattenConcat] operators. They are the
most direct analogues of the corresponding sequence operators. They wait for the inner flow to complete before
starting to collect the next one as the following example shows:

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*

fun requestFlow(i: Int): Flow<String> = flow {
    emit("$i: First") 
    delay(500) // wait 500 ms
    emit("$i: Second")    
}

fun main() = runBlocking<Unit> { 
//sampleStart
    val startTime = System.currentTimeMillis() // remember the start time 
    (1..3).asFlow().onEach { delay(100) } // emit a number every 100 ms 
        .flatMapConcat { requestFlow(it) }                                                                           
        .collect { value -> // collect and print 
            println("$value at ${System.currentTimeMillis() - startTime} ms from start") 
        } 
//sampleEnd
}
```
{kotlin-runnable="true" kotlin-min-compiler-version="1.3"}
<!--- KNIT example-flow-12.kt -->
> You can get the full code [here](https://github.com/Kotlin/kotlinx.coroutines/blob/master/kotlinx-coroutines-core/jvm/test/guide/example-flow-23.kt).
>
{style="note"}

The sequential nature of [flatMapConcat] is clearly seen in the output:

```text                      
1: First at 121 ms from start
1: Second at 622 ms from start
2: First at 727 ms from start
2: Second at 1227 ms from start
3: First at 1328 ms from start
3: Second at 1829 ms from start
```

<!--- TEST ARBITRARY_TIME -->

### flatMapMerge

Another flattening operation is to concurrently collect all the incoming flows and merge their values into
a single flow so that values are emitted as soon as possible.
It is implemented by [flatMapMerge] and [flattenMerge] operators. They both accept an optional
`concurrency` parameter that limits the number of concurrent flows that are collected at the same time
(it is equal to [DEFAULT_CONCURRENCY] by default).

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*

fun requestFlow(i: Int): Flow<String> = flow {
    emit("$i: First") 
    delay(500) // wait 500 ms
    emit("$i: Second")    
}

fun main() = runBlocking<Unit> { 
//sampleStart
    val startTime = System.currentTimeMillis() // remember the start time 
    (1..3).asFlow().onEach { delay(100) } // a number every 100 ms 
        .flatMapMerge { requestFlow(it) }                                                                           
        .collect { value -> // collect and print 
            println("$value at ${System.currentTimeMillis() - startTime} ms from start") 
        } 
//sampleEnd
}
```
{kotlin-runnable="true" kotlin-min-compiler-version="1.3"}
<!--- KNIT example-flow-13.kt -->
> You can get the full code [here](https://github.com/Kotlin/kotlinx.coroutines/blob/master/kotlinx-coroutines-core/jvm/test/guide/example-flow-24.kt).
>
{style="note"}

The concurrent nature of [flatMapMerge] is obvious:

```text                      
1: First at 136 ms from start
2: First at 231 ms from start
3: First at 333 ms from start
1: Second at 639 ms from start
2: Second at 732 ms from start
3: Second at 833 ms from start
```                                               

<!--- TEST ARBITRARY_TIME -->

> Note that the [flatMapMerge] calls its block of code (`{ requestFlow(it) }` in this example) sequentially, but
> collects the resulting flows concurrently, it is the equivalent of performing a sequential
> `map { requestFlow(it) }` first and then calling [flattenMerge] on the result.
>
{style="note"}

### flatMapLatest

In a similar way to the [collectLatest] operator, that was described in the section
["Processing the latest value"](#processing-the-latest-value), there is the corresponding "Latest"
flattening mode where the collection of the previous flow is cancelled as soon as new flow is emitted.
It is implemented by the [flatMapLatest] operator.

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*

fun requestFlow(i: Int): Flow<String> = flow {
    emit("$i: First") 
    delay(500) // wait 500 ms
    emit("$i: Second")    
}

fun main() = runBlocking<Unit> { 
//sampleStart
    val startTime = System.currentTimeMillis() // remember the start time 
    (1..3).asFlow().onEach { delay(100) } // a number every 100 ms 
        .flatMapLatest { requestFlow(it) }                                                                           
        .collect { value -> // collect and print 
            println("$value at ${System.currentTimeMillis() - startTime} ms from start") 
        } 
//sampleEnd
}
```
{kotlin-runnable="true" kotlin-min-compiler-version="1.3"}
<!--- KNIT example-flow-14.kt -->
> You can get the full code [here](https://github.com/Kotlin/kotlinx.coroutines/blob/master/kotlinx-coroutines-core/jvm/test/guide/example-flow-25.kt).
>
{style="note"}

The output here in this example is a good demonstration of how [flatMapLatest] works:

```text                      
1: First at 142 ms from start
2: First at 322 ms from start
3: First at 425 ms from start
3: Second at 931 ms from start
```                                               

<!--- TEST ARBITRARY_TIME -->

> Note that [flatMapLatest] cancels all the code in its block (`{ requestFlow(it) }` in this example) when a new value
> is received.
> It makes no difference in this particular example, because the call to `requestFlow` itself is fast, not-suspending,
> and cannot be cancelled. However, a differnce in output would be visible if we were to use suspending functions
> like `delay` in `requestFlow`.
>
{style="note"}

## Flow completion

When flow collection completes (normally or exceptionally) it may need to execute an action.
As you may have already noticed, it can be done in two ways: imperative or declarative.

### Imperative finally block

In addition to `try`/`catch`, a collector can also use a `finally` block to execute an action
upon `collect` completion.

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*

//sampleStart
fun simple(): Flow<Int> = (1..3).asFlow()

fun main() = runBlocking<Unit> {
    try {
        simple().collect { value -> println(value) }
    } finally {
        println("Done")
    }
}            
//sampleEnd
```
{kotlin-runnable="true" kotlin-min-compiler-version="1.3"}
<!--- KNIT example-flow-15.kt -->
> You can get the full code [here](https://github.com/Kotlin/kotlinx.coroutines/blob/master/kotlinx-coroutines-core/jvm/test/guide/example-flow-31.kt).
>
{style="note"}

This code prints three numbers produced by the `simple` flow followed by a "Done" string:

```text
1
2
3
Done
```

<!--- TEST  -->

### Declarative handling

For the declarative approach, flow has [onCompletion] intermediate operator that is invoked
when the flow has completely collected.

The previous example can be rewritten using an [onCompletion] operator and produces the same output:

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*

fun simple(): Flow<Int> = (1..3).asFlow()

fun main() = runBlocking<Unit> {
//sampleStart
    simple()
        .onCompletion { println("Done") }
        .collect { value -> println(value) }
//sampleEnd
}            
```
{kotlin-runnable="true" kotlin-min-compiler-version="1.3"}
<!--- KNIT example-flow-16.kt -->
> You can get the full code [here](https://github.com/Kotlin/kotlinx.coroutines/blob/master/kotlinx-coroutines-core/jvm/test/guide/example-flow-32.kt).
>
{style="note"}

<!--- TEST 
1
2
3
Done
-->

The key advantage of [onCompletion] is a nullable `Throwable` parameter of the lambda that can be used
to determine whether the flow collection was completed normally or exceptionally. In the following
example the `simple` flow throws an exception after emitting the number 1:

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*

//sampleStart
fun simple(): Flow<Int> = flow {
    emit(1)
    throw RuntimeException()
}

fun main() = runBlocking<Unit> {
    simple()
        .onCompletion { cause -> if (cause != null) println("Flow completed exceptionally") }
        .catch { cause -> println("Caught exception") }
        .collect { value -> println(value) }
}            
//sampleEnd
```
{kotlin-runnable="true" kotlin-min-compiler-version="1.3"}
<!--- KNIT example-flow-17.kt -->
> You can get the full code [here](https://github.com/Kotlin/kotlinx.coroutines/blob/master/kotlinx-coroutines-core/jvm/test/guide/example-flow-33.kt).
>
{style="note"}

As you may expect, it prints:

```text
1
Flow completed exceptionally
Caught exception
```

<!--- TEST -->

The [onCompletion] operator, unlike [catch], does not handle the exception. As we can see from the above
example code, the exception still flows downstream. It will be delivered to further `onCompletion` operators
and can be handled with a `catch` operator.

### Successful completion

Another difference with [catch] operator is that [onCompletion] sees all exceptions and receives
a `null` exception only on successful completion of the upstream flow (without cancellation or failure).

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*

//sampleStart
fun simple(): Flow<Int> = (1..3).asFlow()

fun main() = runBlocking<Unit> {
    simple()
        .onCompletion { cause -> println("Flow completed with $cause") }
        .collect { value ->
            check(value <= 1) { "Collected $value" }                 
            println(value) 
        }
}
//sampleEnd
```
{kotlin-runnable="true" kotlin-min-compiler-version="1.3"}
<!--- KNIT example-flow-18.kt -->
> You can get the full code [here](https://github.com/Kotlin/kotlinx.coroutines/blob/master/kotlinx-coroutines-core/jvm/test/guide/example-flow-34.kt).
>
{style="note"}

We can see the completion cause is not null, because the flow was aborted due to downstream exception:

```text 
1
Flow completed with java.lang.IllegalStateException: Collected 2
Exception in thread "main" java.lang.IllegalStateException: Collected 2
```

<!--- TEST EXCEPTION -->

## Launching flow

It is easy to use flows to represent asynchronous events that are coming from some source.
In this case, we need an analogue of the `addEventListener` function that registers a piece of code with a reaction
for incoming events and continues further work. The [onEach] operator can serve this role.
However, `onEach` is an intermediate operator. We also need a terminal operator to collect the flow.
Otherwise, just calling `onEach` has no effect.

If we use the [collect] terminal operator after `onEach`, then the code after it will wait until the flow is collected:

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*

//sampleStart
// Imitate a flow of events
fun events(): Flow<Int> = (1..3).asFlow().onEach { delay(100) }

fun main() = runBlocking<Unit> {
    events()
        .onEach { event -> println("Event: $event") }
        .collect() // <--- Collecting the flow waits
    println("Done")
}            
//sampleEnd
```
{kotlin-runnable="true" kotlin-min-compiler-version="1.3"}
<!--- KNIT example-flow-19.kt -->
> You can get the full code [here](https://github.com/Kotlin/kotlinx.coroutines/blob/master/kotlinx-coroutines-core/jvm/test/guide/example-flow-35.kt).
>
{style="note"}

As you can see, it prints:

```text 
Event: 1
Event: 2
Event: 3
Done
```    

<!--- TEST -->

The [launchIn] terminal operator comes in handy here. By replacing `collect` with `launchIn` we can
launch a collection of the flow in a separate coroutine, so that execution of further code
immediately continues:

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*

// Imitate a flow of events
fun events(): Flow<Int> = (1..3).asFlow().onEach { delay(100) }

//sampleStart
fun main() = runBlocking<Unit> {
    events()
        .onEach { event -> println("Event: $event") }
        .launchIn(this) // <--- Launching the flow in a separate coroutine
    println("Done")
}            
//sampleEnd
```
{kotlin-runnable="true" kotlin-min-compiler-version="1.3"}
<!--- KNIT example-flow-20.kt -->
> You can get the full code [here](https://github.com/Kotlin/kotlinx.coroutines/blob/master/kotlinx-coroutines-core/jvm/test/guide/example-flow-36.kt).
>
{style="note"}

It prints:

```text          
Done
Event: 1
Event: 2
Event: 3
```    

<!--- TEST -->

The required parameter to `launchIn` must specify a [CoroutineScope] in which the coroutine to collect the flow is
launched. In the above example this scope comes from the [runBlocking]
coroutine builder, so while the flow is running, this [runBlocking] scope waits for completion of its child coroutine
and keeps the main function from returning and terminating this example.

In actual applications a scope will come from an entity with a limited
lifetime. As soon as the lifetime of this entity is terminated the corresponding scope is cancelled, cancelling
the collection of the corresponding flow. This way the pair of `onEach { ... }.launchIn(scope)` works
like the `addEventListener`. However, there is no need for the corresponding `removeEventListener` function,
as cancellation and structured concurrency serve this purpose.

Note that [launchIn] also returns a [Job], which can be used to [cancel][Job.cancel] the corresponding flow collection
coroutine only without cancelling the whole scope or to [join][Job.join] it.

<!-- stdlib references -->

[collections]: https://kotlinlang.org/docs/reference/collections-overview.html
[List]: https://kotlinlang.org/api/latest/jvm/stdlib/kotlin.collections/-list/
[forEach]: https://kotlinlang.org/api/latest/jvm/stdlib/kotlin.collections/for-each.html
[Sequence]: https://kotlinlang.org/api/latest/jvm/stdlib/kotlin.sequences/
[Sequence.zip]: https://kotlinlang.org/api/latest/jvm/stdlib/kotlin.sequences/zip.html
[Sequence.flatten]: https://kotlinlang.org/api/latest/jvm/stdlib/kotlin.sequences/flatten.html
[Sequence.flatMap]: https://kotlinlang.org/api/latest/jvm/stdlib/kotlin.sequences/flat-map.html
[exceptions]: https://kotlinlang.org/docs/reference/exceptions.html

<!--- MODULE kotlinx-coroutines-core -->
<!--- INDEX kotlinx.coroutines -->

[CoroutineDispatcher]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-coroutine-dispatcher/index.html
[CoroutineScope]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-coroutine-scope/index.html
[runBlocking]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/run-blocking.html
[Job]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-job/index.html
[Job.cancel]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/cancel.html
[Job.join]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-job/join.html

<!--- INDEX kotlinx.coroutines.flow -->

[map]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/map.html
[filter]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/filter.html
[transform]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/transform.html
[FlowCollector.emit]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/-flow-collector/emit.html
[take]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/take.html
[collect]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/collect.html
[toList]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/to-list.html
[toSet]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/to-set.html
[first]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/first.html
[single]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/single.html
[reduce]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/reduce.html
[fold]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/fold.html
[buffer]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/buffer.html
[flowOn]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/flow-on.html
[conflate]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/conflate.html
[collectLatest]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/collect-latest.html
[zip]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/zip.html
[combine]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/combine.html
[onEach]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/on-each.html
[flatMapConcat]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/flat-map-concat.html
[flattenConcat]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/flatten-concat.html
[flatMapMerge]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/flat-map-merge.html
[flattenMerge]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/flatten-merge.html
[DEFAULT_CONCURRENCY]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/-d-e-f-a-u-l-t_-c-o-n-c-u-r-r-e-n-c-y.html
[flatMapLatest]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/flat-map-latest.html
[onCompletion]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/on-completion.html
[catch]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/catch.html
[launchIn]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/launch-in.html

<!--- END -->
