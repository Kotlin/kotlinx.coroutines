<!--- TEST_NAME FlowGuideTest --> 

**Table of contents**

<!--- TOC -->

* [Asynchronous Flow](#asynchronous-flow)
  * [Representing multiple values](#representing-multiple-values)
    * [Sequences](#sequences)
    * [Suspending functions](#suspending-functions)
    * [Flows](#flows)
  * [Flows are cold](#flows-are-cold)
  * [Flow cancellation](#flow-cancellation)
  * [Flow builders](#flow-builders)
  * [Intermediate flow operators](#intermediate-flow-operators)
    * [Transform operator](#transform-operator)
    * [Size-limiting operators](#size-limiting-operators)
  * [Terminal flow operators](#terminal-flow-operators)
  * [Flows are sequential](#flows-are-sequential)
  * [Flow context](#flow-context)
    * [Wrong emission withContext](#wrong-emission-withcontext)
    * [flowOn operator](#flowon-operator)
  * [Buffering](#buffering)
    * [Conflation](#conflation)
    * [Processing the latest value](#processing-the-latest-value)
  * [Composing multiple flows](#composing-multiple-flows)
    * [Zip](#zip)
    * [Combine](#combine)
  * [Flattening flows](#flattening-flows)
    * [flatMapConcat](#flatmapconcat)
    * [flatMapMerge](#flatmapmerge)
    * [flatMapLatest](#flatmaplatest)
  * [Flow exceptions](#flow-exceptions)
    * [Collector try and catch](#collector-try-and-catch)
    * [Everything is caught](#everything-is-caught)
  * [Exception transparency](#exception-transparency)
    * [Transparent catch](#transparent-catch)
    * [Catching declaratively](#catching-declaratively)
  * [Flow completion](#flow-completion)
    * [Imperative finally block](#imperative-finally-block)
    * [Declarative handling](#declarative-handling)
    * [Upstream exceptions only](#upstream-exceptions-only)
  * [Imperative versus declarative](#imperative-versus-declarative)
  * [Launching flow](#launching-flow)
  * [Flow and Reactive Streams](#flow-and-reactive-streams)

<!--- END -->

## Asynchronous Flow

Suspending functions asynchronously returns a single value, but how can we return
multiple asynchronously computed values? This is where Kotlin Flows come in.

### Representing multiple values

Multiple values can be represented in Kotlin using [collections]. 
For example, we can have a function `foo()` that returns a [List] 
of three numbers and then print them all using [forEach]:

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

```kotlin
fun foo(): List<Int> = listOf(1, 2, 3)
 
fun main() {
    foo().forEach { value -> println(value) } 
}
```

</div>

> You can get the full code from [here](../kotlinx-coroutines-core/jvm/test/guide/example-flow-01.kt).

This code outputs:

```text
1
2
3
```

<!--- TEST -->

#### Sequences

If we are computing the numbers with some CPU-consuming blocking code 
(each computation taking 100ms), then we can represent the numbers using a [Sequence]:

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

```kotlin
fun foo(): Sequence<Int> = sequence { // sequence builder
    for (i in 1..3) {
        Thread.sleep(100) // pretend we are computing it
        yield(i) // yield next value
    }
}

fun main() {
    foo().forEach { value -> println(value) } 
}
```  

</div>

> You can get the full code from [here](../kotlinx-coroutines-core/jvm/test/guide/example-flow-02.kt).

This code outputs the same numbers, but it waits 100ms before printing each one.

<!--- TEST 
1
2
3
-->

#### Suspending functions

However, this computation blocks the main thread that is running the code. 
When these values are computed by asynchronous code we can mark the function `foo` with a `suspend` modifier,
so that it can perform its work without blocking and return the result as a list:

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

```kotlin
import kotlinx.coroutines.*                 
                           
//sampleStart
suspend fun foo(): List<Int> {
    delay(1000) // pretend we are doing something asynchronous here
    return listOf(1, 2, 3)
}

fun main() = runBlocking<Unit> {
    foo().forEach { value -> println(value) } 
}
//sampleEnd
```  

</div>

> You can get the full code from [here](../kotlinx-coroutines-core/jvm/test/guide/example-flow-03.kt).

This code prints the numbers after waiting for a second.

<!--- TEST 
1
2
3
-->

#### Flows

Using the `List<Int>` result type, means we can only return all the values at once. To represent
the stream of values that are being asynchronously computed, we can use a [`Flow<Int>`][Flow] type just like we would the `Sequence<Int>` type for synchronously computed values:

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*

//sampleStart               
fun foo(): Flow<Int> = flow { // flow builder
    for (i in 1..3) {
        delay(100) // pretend we are doing something useful here
        emit(i) // emit next value
    }
}

fun main() = runBlocking<Unit> {
    // Launch a concurrent coroutine to check if the main thread is blocked
    launch {
        for (k in 1..3) {
            println("I'm not blocked $k")
            delay(100)
        }
    }
    // Collect the flow
    foo().collect { value -> println(value) } 
}
//sampleEnd
```  

</div>

> You can get the full code from [here](../kotlinx-coroutines-core/jvm/test/guide/example-flow-04.kt).

This code waits 100ms before printing each number without blocking the main thread. This is verified
by printing "I'm not blocked" every 100ms from a separate coroutine that is running in the main thread:

```text
I'm not blocked 1
1
I'm not blocked 2
2
I'm not blocked 3
3
```

<!--- TEST -->

Notice the following differences in the code with the [Flow] from the earlier examples:

* A builder function for [Flow] type is called [flow].
* Code inside the `flow { ... }` builder block can suspend.
* The function `foo()` is no longer marked with `suspend` modifier.   
* Values are _emitted_ from the flow using [emit][FlowCollector.emit] function.
* Values are _collected_ from the flow using [collect][collect] function.  

> We can replace [delay] with `Thread.sleep` in the body of `foo`'s `flow { ... }` and see that the main
thread is blocked in this case. 

### Flows are cold

Flows are _cold_ streams similar to sequences &mdash; the code inside a [flow] builder does not
run until the flow is collected. This becomes clear in the following example:

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*

//sampleStart      
fun foo(): Flow<Int> = flow { 
    println("Flow started")
    for (i in 1..3) {
        delay(100)
        emit(i)
    }
}

fun main() = runBlocking<Unit> {
    println("Calling foo...")
    val flow = foo()
    println("Calling collect...")
    flow.collect { value -> println(value) } 
    println("Calling collect again...")
    flow.collect { value -> println(value) } 
}
//sampleEnd
```  

</div>

> You can get the full code from [here](../kotlinx-coroutines-core/jvm/test/guide/example-flow-05.kt).

Which prints:

```text
Calling foo...
Calling collect...
Flow started
1
2
3
Calling collect again...
Flow started
1
2
3
```

<!--- TEST -->
 
This is a key reason the `foo()` function (which returns a flow) is not marked with `suspend` modifier.
By itself, `foo()` returns quickly and does not wait for anything. The flow starts every time it is collected,
that is why we see "Flow started" when we call `collect` again.

### Flow cancellation

Flow adheres to the general cooperative cancellation of coroutines. However, flow infrastructure does not introduce
additional cancellation points. It is fully transparent for cancellation. As usual, flow collection can be 
cancelled when the flow is suspended in a cancellable suspending function (like [delay]), and cannot be cancelled otherwise.

The following example shows how the flow gets cancelled on a timeout when running in a [withTimeoutOrNull] block 
and stops executing its code:

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*

//sampleStart           
fun foo(): Flow<Int> = flow { 
    for (i in 1..3) {
        delay(100)          
        println("Emitting $i")
        emit(i)
    }
}

fun main() = runBlocking<Unit> {
    withTimeoutOrNull(250) { // Timeout after 250ms 
        foo().collect { value -> println(value) } 
    }
    println("Done")
}
//sampleEnd
```  

</div>

> You can get the full code from [here](../kotlinx-coroutines-core/jvm/test/guide/example-flow-06.kt).

Notice how only two numbers get emitted by the flow in `foo()` function, producing the following output: 

```text
Emitting 1
1
Emitting 2
2
Done
```

<!--- TEST -->

### Flow builders

The `flow { ... }` builder from the previous examples is the most basic one. There are other builders for
easier declaration of flows:

* [flowOf] builder that defines a flow emitting a fixed set of values.
* Various collections and sequences can be converted to flows using `.asFlow()` extension functions.

So, the example that prints the numbers from 1 to 3 from a flow can be written as:

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*

fun main() = runBlocking<Unit> {
//sampleStart
    // Convert an integer range to a flow
    (1..3).asFlow().collect { value -> println(value) }
//sampleEnd 
}
```  

</div>

> You can get the full code from [here](../kotlinx-coroutines-core/jvm/test/guide/example-flow-07.kt).
 
<!--- TEST
1
2
3
-->

### Intermediate flow operators

Flows can be transformed with operators, just as you would with collections and sequences. 
Intermediate operators are applied to an upstream flow and return a downstream flow. 
These operators are cold, just like flows are. A call to such an operator is not
a suspending function itself. It works quickly, returning the definition of a new transformed flow. 

The basic operators have familiar names like [map] and [filter]. 
The important difference to sequences is that blocks of 
code inside these operators can call suspending functions. 

For example, a flow of incoming requests can be
mapped to the results with the [map] operator, even when performing a request is a long-running
operation that is implemented by a suspending function:   

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

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

</div>

> You can get the full code from [here](../kotlinx-coroutines-core/jvm/test/guide/example-flow-08.kt).

It produces the following three lines, each line appearing after each second:

```text                                                                    
response 1
response 2
response 3
```

<!--- TEST -->

#### Transform operator

Among the flow transformation operators, the most general one is called [transform]. It can be used to imitate
simple transformations like [map] and [filter], as well as implement more complex transformations. 
Using the `transform` operator, we can [emit][FlowCollector.emit] arbitrary values an arbitrary number of times.

For example, using `transform` we can emit a string before performing a long-running asynchronous request 
and follow it with a response:

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

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

</div>

> You can get the full code from [here](../kotlinx-coroutines-core/jvm/test/guide/example-flow-09.kt).

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

#### Size-limiting operators

Size-limiting intermediate operators like [take] cancel the execution of the flow when the corresponding limit
is reached. Cancellation in coroutines is always performed by throwing an exception, so that all the resource-management
functions (like `try { ... } finally { ... }` blocks) operate normally in case of cancellation:

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

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

</div>

> You can get the full code from [here](../kotlinx-coroutines-core/jvm/test/guide/example-flow-10.kt).

The output of this code clearly shows that the execution of the `flow { ... }` body in the `numbers()` function
stopped after emitting the second number:

```text       
1
2
Finally in numbers
```

<!--- TEST -->

### Terminal flow operators

Terminal operators on flows are _suspending functions_ that start a collection of the flow.
The [collect] operator is the most basic one, but there are other terminal operators, which can make it easier:

* Conversion to various collections like [toList] and [toSet].
* Operators to get the [first] value and to ensure that a flow emits a [single] value.
* Reducing a flow to a value with [reduce] and [fold].

For example:

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

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

</div>

> You can get the full code from [here](../kotlinx-coroutines-core/jvm/test/guide/example-flow-11.kt).

Prints a single number:

```text
55
```

<!--- TEST -->

### Flows are sequential

Each individual collection of a flow is performed sequentially unless special operators that operate
on multiple flows are used. The collection works directly in the coroutine that calls a terminal operator. 
No new coroutines are launched by default. 
Each emitted value is processed by all the intermediate operators from 
upstream to downstream and is then delivered to the terminal operator after. 

See the following example that filters the even integers and maps them to strings:

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*

fun main() = runBlocking<Unit> {
//sampleStart         
    (1..5).asFlow()
        .filter {
            println("Filter $it")
            it % 2 == 0              
        }              
        .map { 
            println("Map $it")
            "string $it"
        }.collect { 
            println("Collect $it")
        }    
//sampleEnd                  
}
```  

</div>

> You can get the full code from [here](../kotlinx-coroutines-core/jvm/test/guide/example-flow-12.kt).

Producing:

```text
Filter 1
Filter 2
Map 2
Collect string 2
Filter 3
Filter 4
Map 4
Collect string 4
Filter 5
```

<!--- TEST -->

### Flow context

Collection of a flow always happens in the context of the calling coroutine. For example, if there is 
a `foo` flow, then the following code runs in the context specified
by the author of this code, regardless of the implementation details of the `foo` flow:

<div class="sample" markdown="1" theme="idea" data-highlight-only>

```kotlin
withContext(context) {
    foo.collect { value ->
        println(value) // run in the specified context 
    }
}
``` 

</div>

<!--- CLEAR -->

This property of a flow is called _context preservation_.

So, by default, code in the `flow { ... }` builder runs in the context that is provided by a collector
of the corresponding flow. For example, consider the implementation of `foo` that prints the thread
it is called on and emits three numbers:

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*

fun log(msg: String) = println("[${Thread.currentThread().name}] $msg")
           
//sampleStart
fun foo(): Flow<Int> = flow {
    log("Started foo flow")
    for (i in 1..3) {
        emit(i)
    }
}  

fun main() = runBlocking<Unit> {
    foo().collect { value -> log("Collected $value") } 
}            
//sampleEnd
```                

</div>

> You can get the full code from [here](../kotlinx-coroutines-core/jvm/test/guide/example-flow-13.kt).

Running this code produces:

```text  
[main @coroutine#1] Started foo flow
[main @coroutine#1] Collected 1
[main @coroutine#1] Collected 2
[main @coroutine#1] Collected 3
```

<!--- TEST FLEXIBLE_THREAD -->

Since `foo().collect` is called from the main thread, the body of `foo`'s flow is also called in the main thread.
This is the perfect default for fast-running or asynchronous code that does not care about the execution context and
does not block the caller. 

#### Wrong emission withContext

However, the long-running CPU-consuming code might need to be executed in the context of [Dispatchers.Default] and UI-updating
code might need to be executed in the context of [Dispatchers.Main]. Usually, [withContext] is used
to change the context in the code using Kotlin coroutines, but code in the `flow { ... }` builder has to honor the context
preservation property and is not allowed to [emit][FlowCollector.emit] from a different context. 

Try running the following code:

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
                      
//sampleStart
fun foo(): Flow<Int> = flow {
    // The WRONG way to change context for CPU-consuming code in flow builder
    kotlinx.coroutines.withContext(Dispatchers.Default) {
        for (i in 1..3) {
            Thread.sleep(100) // pretend we are computing it in CPU-consuming way
            emit(i) // emit next value
        }
    }
}

fun main() = runBlocking<Unit> {
    foo().collect { value -> println(value) } 
}            
//sampleEnd
```  

</div>

> You can get the full code from [here](../kotlinx-coroutines-core/jvm/test/guide/example-flow-14.kt).

This code produces the following exception:

```text
Exception in thread "main" java.lang.IllegalStateException: Flow invariant is violated:
		Flow was collected in [CoroutineId(1), "coroutine#1":BlockingCoroutine{Active}@5511c7f8, BlockingEventLoop@2eac3323],
		but emission happened in [CoroutineId(1), "coroutine#1":DispatchedCoroutine{Active}@2dae0000, DefaultDispatcher].
		Please refer to 'flow' documentation or use 'flowOn' instead
	at ...
``` 

<!--- TEST EXCEPTION -->

#### flowOn operator
   
The exception refers to the [flowOn] function that shall be used to change the context of the flow emission.
The correct way to change the context of a flow is shown in the example below, which also prints the 
names of the corresponding threads to show how it all works:

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*

fun log(msg: String) = println("[${Thread.currentThread().name}] $msg")
           
//sampleStart
fun foo(): Flow<Int> = flow {
    for (i in 1..3) {
        Thread.sleep(100) // pretend we are computing it in CPU-consuming way
        log("Emitting $i")
        emit(i) // emit next value
    }
}.flowOn(Dispatchers.Default) // RIGHT way to change context for CPU-consuming code in flow builder

fun main() = runBlocking<Unit> {
    foo().collect { value ->
        log("Collected $value") 
    } 
}            
//sampleEnd
```  

</div>

> You can get the full code from [here](../kotlinx-coroutines-core/jvm/test/guide/example-flow-15.kt).
  
Notice how `flow { ... }` works in the background thread, while collection happens in the main thread:   
  
<!--- TEST FLEXIBLE_THREAD
[DefaultDispatcher-worker-1 @coroutine#2] Emitting 1
[main @coroutine#1] Collected 1
[DefaultDispatcher-worker-1 @coroutine#2] Emitting 2
[main @coroutine#1] Collected 2
[DefaultDispatcher-worker-1 @coroutine#2] Emitting 3
[main @coroutine#1] Collected 3
-->

Another thing to observe here is that the [flowOn] operator has changed the default sequential nature of the flow.
Now collection happens in one coroutine ("coroutine#1") and emission happens in another coroutine
("coroutine#2") that is running in another thread concurrently with the collecting coroutine. The [flowOn] operator
creates another coroutine for an upstream flow when it has to change the [CoroutineDispatcher] in its context. 

### Buffering

Running different parts of a flow in different coroutines can be helpful from the standpoint of the overall time it takes 
to collect the flow, especially when long-running asynchronous operations are involved. For example, consider a case when
the emission by `foo()` flow is slow, taking 100 ms to produce an element; and collector is also slow, 
taking 300 ms to process an element. Let's see how long it takes to collect such a flow with three numbers:

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlin.system.*

//sampleStart
fun foo(): Flow<Int> = flow {
    for (i in 1..3) {
        delay(100) // pretend we are asynchronously waiting 100 ms
        emit(i) // emit next value
    }
}

fun main() = runBlocking<Unit> { 
    val time = measureTimeMillis {
        foo().collect { value -> 
            delay(300) // pretend we are processing it for 300 ms
            println(value) 
        } 
    }   
    println("Collected in $time ms")
}
//sampleEnd
```  

</div>

> You can get the full code from [here](../kotlinx-coroutines-core/jvm/test/guide/example-flow-16.kt).

It produces something like this, with the whole collection taking around 1200 ms (three numbers, 400 ms for each):

```text
1
2
3
Collected in 1220 ms
```

<!--- TEST ARBITRARY_TIME -->

We can use a [buffer] operator on a flow to run emitting code of `foo()` concurrently with collecting code,
as opposed to running them sequentially:

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlin.system.*

fun foo(): Flow<Int> = flow {
    for (i in 1..3) {
        delay(100) // pretend we are asynchronously waiting 100 ms
        emit(i) // emit next value
    }
}

fun main() = runBlocking<Unit> { 
//sampleStart
    val time = measureTimeMillis {
        foo()
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

</div>

> You can get the full code from [here](../kotlinx-coroutines-core/jvm/test/guide/example-flow-17.kt).

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
but here we explicitly request buffering without changing the execution context. 

#### Conflation

When a flow represents partial results of the operation or operation status updates, it may not be necessary
to process each value, but instead, only most recent ones. In this case, the [conflate] operator can be used to skip
intermediate values when a collector is too slow to process them. Building on the previous example:

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlin.system.*

fun foo(): Flow<Int> = flow {
    for (i in 1..3) {
        delay(100) // pretend we are asynchronously waiting 100 ms
        emit(i) // emit next value
    }
}

fun main() = runBlocking<Unit> { 
//sampleStart
    val time = measureTimeMillis {
        foo()
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

</div>

> You can get the full code from [here](../kotlinx-coroutines-core/jvm/test/guide/example-flow-18.kt).

We see that while the first number was still being processed the second, and third were already produced, so
the second one was _conflated_ and only the most recent (the third one) was delivered to the collector:

```text
1
3
Collected in 758 ms
```             

<!--- TEST ARBITRARY_TIME -->   

#### Processing the latest value

Conflation is one way to speed up processing when both the emitter and collector are slow. It does it by dropping emitted values.
The other way is to cancel a slow collector and restart it every time a new value is emitted. There is
a family of `xxxLatest` operators that perform the same essential logic of a `xxx` operator, but cancel the
code in their block on a new value. Let's try changing [conflate] to [collectLatest] in the previous example:

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlin.system.*

fun foo(): Flow<Int> = flow {
    for (i in 1..3) {
        delay(100) // pretend we are asynchronously waiting 100 ms
        emit(i) // emit next value
    }
}

fun main() = runBlocking<Unit> { 
//sampleStart
    val time = measureTimeMillis {
        foo()
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

</div>

> You can get the full code from [here](../kotlinx-coroutines-core/jvm/test/guide/example-flow-19.kt).
 
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

### Composing multiple flows

There are lots of ways to compose multiple flows.

#### Zip

Just like the [Sequence.zip] extension function in the Kotlin standard library, 
flows have a [zip] operator that combines the corresponding values of two flows:

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

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

</div>

> You can get the full code from [here](../kotlinx-coroutines-core/jvm/test/guide/example-flow-20.kt).

This example prints:

```text
1 -> one
2 -> two
3 -> three
```
 
<!--- TEST -->

#### Combine

When flow represents the most recent value of a variable or operation (see also the related 
section on [conflation](#conflation)), it might be needed to perform a computation that depends on
the most recent values of the corresponding flows and to recompute it whenever any of the upstream
flows emit a value. The corresponding family of operators is called [combine].

For example, if the numbers in the previous example update every 300ms, but strings update every 400 ms, 
then zipping them using the [zip] operator will still produce the same result, 
albeit results that are printed every 400 ms:

> We use a [onEach] intermediate operator in this example to delay each element and make the code 
that emits sample flows more declarative and shorter.
 
<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

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

</div>

> You can get the full code from [here](../kotlinx-coroutines-core/jvm/test/guide/example-flow-21.kt).

<!--- TEST ARBITRARY_TIME
1 -> one at 437 ms from start
2 -> two at 837 ms from start
3 -> three at 1243 ms from start
-->

However, when using a [combine] operator here instead of a [zip]:

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

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

</div>

> You can get the full code from [here](../kotlinx-coroutines-core/jvm/test/guide/example-flow-22.kt).

We get quite a different output, where a line is printed at each emission from either `nums` or `strs` flows:

```text 
1 -> one at 452 ms from start
2 -> one at 651 ms from start
2 -> two at 854 ms from start
3 -> two at 952 ms from start
3 -> three at 1256 ms from start
```

<!--- TEST ARBITRARY_TIME -->

### Flattening flows

Flows represent asynchronously received sequences of values, so it is quite easy to get in a situation where 
each value triggers a request for another sequence of values. For example, we can have the following
function that returns a flow of two strings 500 ms apart:

<div class="sample" markdown="1" theme="idea" data-highlight-only>

```kotlin
fun requestFlow(i: Int): Flow<String> = flow {
    emit("$i: First") 
    delay(500) // wait 500 ms
    emit("$i: Second")    
}
```

</div>

<!--- CLEAR -->

Now if we have a flow of three integers and call `requestFlow` for each of them like this:

<div class="sample" markdown="1" theme="idea" data-highlight-only>

```kotlin
(1..3).asFlow().map { requestFlow(it) }
``` 

</div>

<!--- CLEAR -->

Then we end up with a flow of flows (`Flow<Flow<String>>`) that needs to be _flattened_ into a single flow for 
further processing. Collections and sequences have [flatten][Sequence.flatten] and [flatMap][Sequence.flatMap]
operators for this. However, due the asynchronous nature of flows they call for different _modes_ of flattening, 
as such, there is a family of flattening operators on flows.

#### flatMapConcat

Concatenating mode is implemented by [flatMapConcat] and [flattenConcat] operators. They are the most direct
analogues of the corresponding sequence operators. They wait for the inner flow to complete before
starting to collect the next one as the following example shows:

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

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
        .flatMapConcat { requestFlow(it) }                                                                           
        .collect { value -> // collect and print 
            println("$value at ${System.currentTimeMillis() - startTime} ms from start") 
        } 
//sampleEnd
}
```  

</div>

> You can get the full code from [here](../kotlinx-coroutines-core/jvm/test/guide/example-flow-23.kt).            

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

#### flatMapMerge

Another flattening mode is to concurrently collect all the incoming flows and merge their values into
a single flow so that values are emitted as soon as possible.
It is implemented by [flatMapMerge] and [flattenMerge] operators. They both accept an optional 
`concurrency` parameter that limits the number of concurrent flows that are collected at the same time
(it is equal to [DEFAULT_CONCURRENCY] by default). 

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

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

</div>

> You can get the full code from [here](../kotlinx-coroutines-core/jvm/test/guide/example-flow-24.kt).            

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
collects the resulting flows concurrently, it is the equivalent of performing a sequential 
`map { requestFlow(it) }` first and then calling [flattenMerge] on the result.   

#### flatMapLatest   

In a similar way to the [collectLatest] operator, that was shown in 
["Processing the latest value"](#processing-the-latest-value) section, there is the corresponding "Latest" 
flattening mode where a collection of the previous flow is cancelled as soon as new flow is emitted. 
It is implemented by the [flatMapLatest] operator.

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

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

</div>

> You can get the full code from [here](../kotlinx-coroutines-core/jvm/test/guide/example-flow-25.kt).            

The output here in this example is a good demonstration of how [flatMapLatest] works:

```text                      
1: First at 142 ms from start
2: First at 322 ms from start
3: First at 425 ms from start
3: Second at 931 ms from start
```                                               

<!--- TEST ARBITRARY_TIME -->
  
> Note that [flatMapLatest] cancels all the code in its block (`{ requestFlow(it) }` in this example) on a new value. 
It makes no difference in this particular example, because the call to `requestFlow` itself is fast, not-suspending,
and cannot be cancelled. However, it would show up if we were to use suspending functions like `delay` in there.

### Flow exceptions

Flow collection can complete with an exception when an emitter or code inside the operators throw an exception. 
There are several ways to handle these exceptions.

#### Collector try and catch

A collector can use Kotlin's [`try/catch`][exceptions] block to handle exceptions: 

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*

//sampleStart
fun foo(): Flow<Int> = flow {
    for (i in 1..3) {
        println("Emitting $i")
        emit(i) // emit next value
    }
}

fun main() = runBlocking<Unit> {
    try {
        foo().collect { value ->         
            println(value)
            check(value <= 1) { "Collected $value" }
        }
    } catch (e: Throwable) {
        println("Caught $e")
    } 
}            
//sampleEnd
```  

</div>

> You can get the full code from [here](../kotlinx-coroutines-core/jvm/test/guide/example-flow-26.kt).

This code successfully catches an exception in [collect] terminal operator and, 
as we see, no more values are emitted after that:

```text 
Emitting 1
1
Emitting 2
2
Caught java.lang.IllegalStateException: Collected 2
```

<!--- TEST -->

#### Everything is caught

The previous example actually catches any exception happening in the emitter or in any intermediate or terminal operators.
For example, let's change the code so that emitted values are [mapped][map] to strings,
but the corresponding code produces an exception:

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*

//sampleStart
fun foo(): Flow<String> = 
    flow {
        for (i in 1..3) {
            println("Emitting $i")
            emit(i) // emit next value
        }
    }
    .map { value ->
        check(value <= 1) { "Crashed on $value" }                 
        "string $value"
    }

fun main() = runBlocking<Unit> {
    try {
        foo().collect { value -> println(value) }
    } catch (e: Throwable) {
        println("Caught $e")
    } 
}            
//sampleEnd
```  

</div>

> You can get the full code from [here](../kotlinx-coroutines-core/jvm/test/guide/example-flow-27.kt).

This exception is still caught and collection is stopped:

```text 
Emitting 1
string 1
Emitting 2
Caught java.lang.IllegalStateException: Crashed on 2
```

<!--- TEST -->

### Exception transparency

But how can code of the emitter encapsulate its exception handling behavior?  

Flows must be _transparent to exceptions_ and it is a violation of the exception transparency to [emit][FlowCollector.emit] values in the 
`flow { ... }` builder from inside of a `try/catch` block. This guarantees that a collector throwing an exception
can always catch it using `try/catch` as in the previous example.

The emitter can use a [catch] operator that preserves this exception transparency and allows encapsulation
of its exception handling. The body of the `catch` operator can analyze an exception
and react to it in different ways depending on which exception was caught:

* Exceptions can be rethrown using `throw`.
* Exceptions can be turned into emission of values using [emit][FlowCollector.emit] from the body of [catch].
* Exceptions can be ignored, logged, or processed by some other code.

For example, let us emit the text on catching an exception:

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*

fun foo(): Flow<String> = 
    flow {
        for (i in 1..3) {
            println("Emitting $i")
            emit(i) // emit next value
        }
    }
    .map { value ->
        check(value <= 1) { "Crashed on $value" }                 
        "string $value"
    }

fun main() = runBlocking<Unit> {
//sampleStart
    foo()
        .catch { e -> emit("Caught $e") } // emit on exception
        .collect { value -> println(value) }
//sampleEnd
}            
```  

</div>

> You can get the full code from [here](../kotlinx-coroutines-core/jvm/test/guide/example-flow-28.kt). 
 
The output of the example is the same, even though we do not have `try/catch` around the code anymore. 

<!--- TEST  
Emitting 1
string 1
Emitting 2
Caught java.lang.IllegalStateException: Crashed on 2
-->

#### Transparent catch

The [catch] intermediate operator, honoring exception transparency, catches only upstream exceptions
(that is an exception from all the operators above `catch`, but not below it).
If the block in `collect { ... }` (placed below `catch`) throws an exception then it escapes:  

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*

//sampleStart
fun foo(): Flow<Int> = flow {
    for (i in 1..3) {
        println("Emitting $i")
        emit(i)
    }
}

fun main() = runBlocking<Unit> {
    foo()
        .catch { e -> println("Caught $e") } // does not catch downstream exceptions
        .collect { value ->
            check(value <= 1) { "Collected $value" }                 
            println(value) 
        }
}            
//sampleEnd
```  

</div>

> You can get the full code from [here](../kotlinx-coroutines-core/jvm/test/guide/example-flow-29.kt). 
 
A "Caught ..." message is not printed despite there being a `catch` operator: 

<!--- TEST EXCEPTION  
Emitting 1
1
Emitting 2
Exception in thread "main" java.lang.IllegalStateException: Collected 2
	at ...
-->

#### Catching declaratively

We can combine the declarative nature of the [catch] operator with a desire to handle all the exceptions, by moving the body
of the [collect] operator into [onEach] and putting it before the `catch` operator. Collection of this flow must
be triggered by a call to `collect()` without parameters:

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*

fun foo(): Flow<Int> = flow {
    for (i in 1..3) {
        println("Emitting $i")
        emit(i)
    }
}

fun main() = runBlocking<Unit> {
//sampleStart
    foo()
        .onEach { value ->
            check(value <= 1) { "Collected $value" }                 
            println(value) 
        }
        .catch { e -> println("Caught $e") }
        .collect()
//sampleEnd
}            
```  

</div>

> You can get the full code from [here](../kotlinx-coroutines-core/jvm/test/guide/example-flow-30.kt). 
 
Now we can see that a "Caught ..." message is printed and so we can catch all the exceptions without explicitly
using a `try/catch` block: 

<!--- TEST EXCEPTION  
Emitting 1
1
Emitting 2
Caught java.lang.IllegalStateException: Collected 2
-->

### Flow completion

When flow collection completes (normally or exceptionally) it may need to execute an action. 
As you may have already noticed, it can be done in two ways: imperative or declarative.

#### Imperative finally block

In addition to `try`/`catch`, a collector can also use a `finally` block to execute an action 
upon `collect` completion.

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*

//sampleStart
fun foo(): Flow<Int> = (1..3).asFlow()

fun main() = runBlocking<Unit> {
    try {
        foo().collect { value -> println(value) }
    } finally {
        println("Done")
    }
}            
//sampleEnd
```  

</div>

> You can get the full code from [here](../kotlinx-coroutines-core/jvm/test/guide/example-flow-31.kt). 

This code prints three numbers produced by the `foo()` flow followed by a "Done" string:

```text
1
2
3
Done
```

<!--- TEST  -->

#### Declarative handling

For the declarative approach, flow has [onCompletion] intermediate operator that is invoked
when the flow has completely collected.

The previous example can be rewritten using an [onCompletion] operator and produces the same output:

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*

fun foo(): Flow<Int> = (1..3).asFlow()

fun main() = runBlocking<Unit> {
//sampleStart
    foo()
        .onCompletion { println("Done") }
        .collect { value -> println(value) }
//sampleEnd
}            
```
</div>

> You can get the full code from [here](../kotlinx-coroutines-core/jvm/test/guide/example-flow-32.kt). 

<!--- TEST 
1
2
3
Done
-->

The key advantage of [onCompletion] is a nullable `Throwable` parameter of the lambda that can be used
to determine whether the flow collection was completed normally or exceptionally. In the following
example the `foo()` flow throws an exception after emitting the number 1:

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*

//sampleStart
fun foo(): Flow<Int> = flow {
    emit(1)
    throw RuntimeException()
}

fun main() = runBlocking<Unit> {
    foo()
        .onCompletion { cause -> if (cause != null) println("Flow completed exceptionally") }
        .catch { cause -> println("Caught exception") }
        .collect { value -> println(value) }
}            
//sampleEnd
```
</div>

> You can get the full code from [here](../kotlinx-coroutines-core/jvm/test/guide/example-flow-33.kt). 

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

#### Upstream exceptions only

Just like the [catch] operator, [onCompletion] only sees exceptions coming from upstream and does not
see downstream exceptions. For example, run the following code:

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*

//sampleStart
fun foo(): Flow<Int> = (1..3).asFlow()

fun main() = runBlocking<Unit> {
    foo()
        .onCompletion { cause -> println("Flow completed with $cause") }
        .collect { value ->
            check(value <= 1) { "Collected $value" }                 
            println(value) 
        }
}
//sampleEnd
```

</div>

> You can get the full code from [here](../kotlinx-coroutines-core/jvm/test/guide/example-flow-34.kt). 

We can see the completion cause is null, yet collection failed with exception:

```text 
1
Flow completed with null
Exception in thread "main" java.lang.IllegalStateException: Collected 2
```

<!--- TEST EXCEPTION -->

### Imperative versus declarative

Now we know how to collect flow, and handle its completion and exceptions in both imperative and declarative ways.
The natural question here is, which approach is preferred and why?
As a library, we do not advocate for any particular approach and believe that both options
are valid and should be selected according to your own preferences and code style. 

### Launching flow

It is easy to use flows to represent asynchronous events that are coming from some source.
In this case, we need an analogue of the `addEventListener` function that registers a piece of code with a reaction
for incoming events and continues further work. The [onEach] operator can serve this role. 
However, `onEach` is an intermediate operator. We also need a terminal operator to collect the flow. 
Otherwise, just calling `onEach` has no effect.
 
If we use the [collect] terminal operator after `onEach`, then the code after it will wait until the flow is collected:

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

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

</div>

> You can get the full code from [here](../kotlinx-coroutines-core/jvm/test/guide/example-flow-35.kt). 
  
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

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

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

</div>

> You can get the full code from [here](../kotlinx-coroutines-core/jvm/test/guide/example-flow-36.kt). 
  
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
 
### Flow and Reactive Streams

For those who are familiar with [Reactive Streams](https://www.reactive-streams.org/) or reactive frameworks such as RxJava and project Reactor, 
design of the Flow may look very familiar.

Indeed, its design was inspired by Reactive Streams and its various implementations. But Flow main goal is to have as simple design as possible, 
be Kotlin and suspension friendly and respect structured concurrency. Achieving this goal would be impossible without reactive pioneers and their tremendous work. You can read the complete story in [Reactive Streams and Kotlin Flows](https://medium.com/@elizarov/reactive-streams-and-kotlin-flows-bfd12772cda4) article.

While being different, conceptually, Flow *is* a reactive stream and it is possible to convert it to the reactive (spec and TCK compliant) Publisher and vice versa.
Such converters are provided by `kotlinx.coroutines` out-of-the-box and can be found in corresponding reactive modules (`kotlinx-coroutines-reactive` for Reactive Streams, `kotlinx-coroutines-reactor` for Project Reactor and `kotlinx-coroutines-rx2` for RxJava2).
Integration modules include conversions from and to `Flow`, integration with Reactor's `Context` and suspension-friendly ways to work with various reactive entities.
 
<!-- stdlib references -->

[collections]: https://kotlinlang.org/docs/reference/collections-overview.html 
[List]: https://kotlinlang.org/api/latest/jvm/stdlib/kotlin.collections/-list/index.html 
[forEach]: https://kotlinlang.org/api/latest/jvm/stdlib/kotlin.collections/for-each.html
[Sequence]: https://kotlinlang.org/api/latest/jvm/stdlib/kotlin.sequences/index.html
[Sequence.zip]: https://kotlinlang.org/api/latest/jvm/stdlib/kotlin.sequences/zip.html
[Sequence.flatten]: https://kotlinlang.org/api/latest/jvm/stdlib/kotlin.sequences/flatten.html
[Sequence.flatMap]: https://kotlinlang.org/api/latest/jvm/stdlib/kotlin.sequences/flat-map.html
[exceptions]: https://kotlinlang.org/docs/reference/exceptions.html

<!--- MODULE kotlinx-coroutines-core -->
<!--- INDEX kotlinx.coroutines -->
[delay]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/delay.html
[withTimeoutOrNull]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/with-timeout-or-null.html
[Dispatchers.Default]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-dispatchers/-default.html
[Dispatchers.Main]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-dispatchers/-main.html
[withContext]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/with-context.html
[CoroutineDispatcher]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-coroutine-dispatcher/index.html
[CoroutineScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-coroutine-scope/index.html
[runBlocking]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/run-blocking.html
[Job]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-job/index.html
[Job.cancel]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-job/cancel.html
[Job.join]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-job/join.html
<!--- INDEX kotlinx.coroutines.flow -->
[Flow]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/-flow/index.html
[flow]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/flow.html
[FlowCollector.emit]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/-flow-collector/emit.html
[collect]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/collect.html
[flowOf]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/flow-of.html
[map]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/map.html
[filter]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/filter.html
[transform]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/transform.html
[take]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/take.html
[toList]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/to-list.html
[toSet]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/to-set.html
[first]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/first.html
[single]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/single.html
[reduce]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/reduce.html
[fold]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/fold.html
[flowOn]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/flow-on.html
[buffer]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/buffer.html
[conflate]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/conflate.html
[collectLatest]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/collect-latest.html
[zip]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/zip.html
[combine]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/combine.html
[onEach]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/on-each.html
[flatMapConcat]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/flat-map-concat.html
[flattenConcat]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/flatten-concat.html
[flatMapMerge]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/flat-map-merge.html
[flattenMerge]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/flatten-merge.html
[DEFAULT_CONCURRENCY]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/-d-e-f-a-u-l-t_-c-o-n-c-u-r-r-e-n-c-y.html
[flatMapLatest]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/flat-map-latest.html
[catch]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/catch.html
[onCompletion]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/on-completion.html
[launchIn]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/launch-in.html
<!--- END -->
