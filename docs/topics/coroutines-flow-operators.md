<contribute-url>https://github.com/Kotlin/kotlinx.coroutines/edit/master/docs/topics/</contribute-url>

[//]: # (title: Flow operators)

Flow operators let you transform and process values in a flow pipeline.
Kotlin provides two main kinds of flow operators:

* [**Intermediate operators**](#intermediate-operators) return a new downstream flow that consumes values from upstream flows and applies an operation to them.
* [**Terminal operators**](#terminal-operators) trigger the execution of the flow pipeline by collecting an upstream flow. They may also return a result.

While the [`kotlinx.coroutines`](https://github.com/Kotlin/kotlinx.coroutines) library offers a wide range of flow operators,
you can also define custom ones when you need behavior that the built-in operators don't provide.

> The following sections include examples for custom implementations alongside the corresponding built-in operators.
>
{style="tip"}

## Intermediate operators

Intermediate operators return a new downstream flow that consumes values from upstream flows.
You can chain several intermediate operators to build a flow pipeline before collecting the final result.

Intermediate operators can be classified by purpose into the following categories:

* [**Transforming operators**](#transforming-operators) transform values before emitting them downstream.
* [**Filtering and size-limiting operators**](#filtering-and-size-limiting-operators) control which upstream values continue downstream.
* [**Concurrent processing operators**](#concurrent-processing-operators) let emissions run separately from collection.
* [**Combining operators**](#combining-operators) collect values from multiple upstream flows and emit them into one downstream flow.
* [**Lifecycle operators**](#lifecycle-operators) run actions in response to specific events during flow collection, such as when collection starts or when the upstream flow completes.


### Transforming operators

Transforming operators transform the values emitted by an upstream flow.
You can use them to convert values to another type, skip values, or emit additional values downstream.

> Transforming operators accept suspending lambdas, so their lambdas can call suspending functions while processing each emitted value.
> They still process values sequentially unless the flow pipeline uses an operator that introduces concurrency.
>
{style="note"}

The [`.transform()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/transform.html) operator is a general transforming operator that you can use as the basis for more specific transforming operators, such as [`.map()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/map.html) and [`.filter()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/filter.html).

Here's an example that uses the `.transform()` operator to emit each upstream value as many times as its value:

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*

// A simplified custom implementation of the default .transform() operator
inline fun <T, R> Flow<T>.myTransform(
    // Accepts a suspending lambda that can emit values downstream
    crossinline transform: suspend FlowCollector<R>.(value: T) -> Unit
): Flow<R> = flow {
    // Collects values from the upstream flow
    this@myTransform.collect { value ->
        // Applies the transformation and emits values to the downstream flow
        this@flow.transform(value)
    }
}

// Uses the default .transform() operator
suspend fun main() = withContext(Dispatchers.Default) {
    val flow = (0..4).asFlow().transform { value ->
        // Emits each value as many times as its value
        repeat(value) {
            emit(value)
        }
    }
    println(flow.toList())
    // [1, 2, 2, 3, 3, 3, 4, 4, 4, 4]
}
```
{kotlin-runnable="true"}

You can use the [`.map()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/map.html) operator to transform each upstream value into one downstream value.

Here's an example that uses `.map()` to multiply each value by four:

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*

// A simplified custom implementation of the default .map() operator
inline fun <T, R> Flow<T>.myMap(
    crossinline transform: suspend (value: T) -> R
): Flow<R> = transform { value ->
    emit(transform(value))
}

//sampleStart
suspend fun main() = withContext(Dispatchers.Default) {
    // Multiplies each upstream value by four
    val flow = (0..4).asFlow().map { it * 4 }
    println(flow.toList())
    // [0, 4, 8, 12, 16]
}
//sampleEnd
```
{kotlin-runnable="true"}

To emit only upstream values that match a condition, use the [`.filter()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/filter.html) operator.

Here's an example that emits values where dividing by `3` leaves a remainder of `1`:

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*

// A simplified custom implementation of the default .filter() operator
inline fun <T> Flow<T>.myFilter(
    crossinline predicate: suspend (value: T) -> Boolean
): Flow<T> = transform { value ->
    // Emits only values that match the condition
    if (predicate(value))
        emit(value)
}

//sampleStart
suspend fun main() = withContext(Dispatchers.Default) {
    // Emits only values where dividing by 3 leaves a remainder of 1
    val flow = (0..10).asFlow().filter { it % 3 == 1 }
    println(flow.toList())
    // [1, 4, 7, 10]
}
//sampleEnd
```
{kotlin-runnable="true"}

Some operators can combine the behavior of other transforming operators, such as `.map()` and `.filter()`, by transforming values and emitting only the results that match a condition.

For example, use [`.mapNotNull()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/map-not-null.html) to transform each upstream value and emit only non-null results:

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*

// A simplified custom implementation of the default .mapNotNull() operator
inline fun <T, R: Any> Flow<T>.myMapNotNull(
    crossinline transform: suspend (value: T) -> R?
): Flow<R> = transform { value ->
    transform(value)?.let { transformed ->
        emit(transformed)
    }
}

//sampleStart
suspend fun main() = withContext(Dispatchers.Default) {
    // Converts each string to Double and skips values that can't be converted
    val flow = flowOf("1.2", "10", "11", "error", "0.000")
        .mapNotNull { it.toDoubleOrNull() }
    
    println(flow.toList())
    // [1.2, 10.0, 11.0, 0.0]
}
//sampleEnd
```
{kotlin-runnable="true"}

### Filtering and size-limiting operators

Filtering and size-limiting operators control which values continue downstream from a flow.
You can use them to remove repeated consecutive values, skip values from the beginning of a flow, or cancel collection after a specified number of values.

To ignore repeated consecutive values, use the [`.distinctUntilChanged()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/distinct-until-changed.html) operator.
It emits a value only when it differs from the previously emitted value:

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*

// A simplified custom version of the default .distinctUntilChanged() operator
fun <T> Flow<T>.myDistinctUntilChanged(): Flow<T> = flow {
    var lastEmitted: Any? = Any() // A value that's equal only to itself
    this@myDistinctUntilChanged.collect { value ->
        if (lastEmitted != value) {
            this@flow.emit(value)
            lastEmitted = value
        }
    }
}

suspend fun main() = withContext(Dispatchers.Default) {
    // Removes repeated consecutive values from the upstream flow
    val flow = flowOf(1, 2, 3, 3, 3, 4, 5, 5, 1).distinctUntilChanged()
    println(flow.toList())
    // [1, 2, 3, 4, 5, 1]
}

```
{kotlin-runnable="true"}

You can use the [`.drop()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/drop.html) operator to skip the first values emitted by an upstream flow.
For example, `.drop(2)` skips the first two values and emits the remaining values downstream:

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*

// A simplified custom version of the default .drop() operator
fun <T> Flow<T>.myDrop(count: Int): Flow<T> = flow {
    require(count >= 0)
    var elementsAlreadyDropped = 0
    this@myDrop.collect { value ->
        if (elementsAlreadyDropped == count) {
            this@flow.emit(value)
        } else {
            ++elementsAlreadyDropped
        }
    }
}

//sampleStart
suspend fun main() = withContext(Dispatchers.Default) {
    // Skips the first two values from the upstream flow    
    val flow = flowOf(1, 2, 3, 4, 5).drop(2)
    println(flow.toList())
    // [3, 4, 5]
}
//sampleEnd
```
{kotlin-runnable="true"}

To cancel collection after a fixed number of values, use the [`.take()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/take.html) operator.
Here's an example that uses the `.take()` operator to collect only the first three values:

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlin.random.*
import java.io.IOException
import kotlin.time.Duration.Companion.milliseconds

// A simplified custom version of the default .take() operator
fun <T> Flow<T>.myTake(count: Int): Flow<T> = flow {
    require(count > 0)
    val cancellationException = CancellationException()
    var elementsRemaining = count
    try {
        this@myTake.collect {
            emit(it)
            --elementsRemaining
            if (elementsRemaining == 0) {
                // Cancels the upstream flow after the requested number of values
                throw cancellationException
            }
        }
    } catch (e: Throwable) {
        if (e === cancellationException) {
            // Handles the CancellationException used to cancel the upstream flow
            // Completes the flow after the set number of values in .myTake()
        } else {
            // Rethrows unexpected exceptions
            throw e
        }
    }
}

//sampleStart
suspend fun main() = withContext(Dispatchers.Default) {
    // Collects only the first three values from the upstream flow
    val flow = (0..1000).asFlow().take(3)

    println(flow.toList())
    // [0, 1, 2]
}
//sampleEnd
```
{kotlin-runnable="true"}

### Concurrent processing operators

By default, a flow pipeline processes values sequentially.
The upstream flow emits a value, and collectors process it before the next value is emitted.

To run the upstream flow concurrently with downstream collection, use concurrent processing operators to introduce a buffer.
A buffer stores values that the upstream flow has emitted, but the collector hasn't processed yet.

One operator that introduces this buffer is the [`.buffer()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/buffer.html) operator.
It lets you configure the buffer capacity and what happens when the buffer is full, for example:

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlin.time.Duration.Companion.milliseconds

//sampleStart
suspend fun main() = withContext(Dispatchers.Default) {
    flow {
        repeat(10) {
            emit(it)
            println("Emitted $it!")
        }
    }
        // Lets the upstream flow emit up to four values ahead of the collector
        .buffer(4)
        .collect {
            println("Processed $it!")
            delay(20.milliseconds)
        }
}
//sampleEnd
```
{kotlin-runnable="true"}

When the collector is slower than the upstream flow, the pipeline needs a way to handle values that the collector hasn't processed yet.

By default, the collector applies *backpressure* to the upstream flow.
With this strategy, the upstream flow suspends when the buffer is full and resumes when the collector frees up space.

To drop values instead of suspending the upstream flow, set the [`onBufferOverflow`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-buffer-overflow/) parameter:

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.BufferOverflow
import kotlinx.coroutines.flow.*
import kotlin.time.Duration.Companion.milliseconds

//sampleStart
suspend fun main() = withContext(Dispatchers.Default) {
    flow {
        repeat(10) {
            emit(it)
            println("Emitted $it!")
        }
    }
        // Stores up to four values before applying the overflow behavior
        // Drops the oldest buffered value when the buffer is full
        .buffer(4, onBufferOverflow = BufferOverflow.DROP_OLDEST)
        .collect { value ->
            println("Processed $value!")
            delay(20.milliseconds)
        }
}
//sampleEnd
```
{kotlin-runnable="true"}

You can also use the [`.conflate()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/conflate.html) operator, which is a shorthand for `buffer(1, onBufferOverflow = BufferOverflow.DROP_OLDEST)`.
Use it when you only want to process the latest values, skipping the values emitted while the previous value is being collected:

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlin.time.Duration.Companion.milliseconds

//sampleStart
suspend fun main() = withContext(Dispatchers.Default) {
    flow {
        repeat(10) {
            emit(it)
            println("Emitted $it!")
        }
    }.conflate().collect {
        println("Processed $it!")
        delay(20.milliseconds)
    }
}
//sampleEnd
```
{kotlin-runnable="true"}

The `.conflate()` operator only affects which buffered values the collector processes.
It doesn't cancel processing that has already started.
To do that, use [`collectLatest()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/collect-latest.html) instead.

In the previous examples, the `.buffer()` and `.conflate()` operators run the upstream flow concurrently in a separate coroutine without changing its coroutine context.

To run the upstream flow in a different coroutine context, use the [`.flowOn()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/flow-on.html) operator.
If this changes the dispatcher, `.flowOn()` collects the upstream flow in a separate coroutine and uses a buffer between upstream emission and downstream collection.

Here's a simplified example that uses `.flowOn()` to run the upstream flow in `Dispatchers.IO`:

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlin.time.Duration.Companion.milliseconds

//sampleStart
suspend fun main() = withContext(Dispatchers.Default) {
    flow {
        repeat(10) {
            emit(it)
        }
        println("Finished emitting!")
    }.flowOn(Dispatchers.IO).collect {
        println("Received $it!")
        delay(10.milliseconds)
    }
}
//sampleEnd
```
{kotlin-runnable="true"}

In this example, the `.flowOn()` operator can introduce concurrent upstream processing, but the buffer behavior isn't configured explicitly.

To configure both the coroutine context of the upstream flow and the buffer behavior, combine `.flowOn()` with `.buffer()` or `.conflate()`.
When you use these operators together, the operators perform *operator fusion* and share a single buffer.

Here's an example that uses `.flowOn(Dispatchers.IO)` to run the upstream flow in `Dispatchers.IO` and `.conflate()` to keep the newest buffered value:

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlin.random.Random
import kotlin.time.Duration.Companion.milliseconds
import kotlin.math.round

//sampleStart
fun awaitSensorSignal(): SensorSignal {
    Thread.sleep(10)
    val reading =
        round(Random.nextDouble(25.0, 100.0) * 100.0)/100.0
    println("Measured $reading as the temperature")
    return SensorSignal(temperatureCelsius = reading)
}

data class SensorSignal(
    val temperatureCelsius: Double
)

suspend fun sendLatestTemperature(temperatureCelsius: Double) {
    println("Starting to send $temperatureCelsius...")
    delay(50.milliseconds)
    println("Sent $temperatureCelsius.")
}

suspend fun main() = withContext(Dispatchers.Default) {
    val smartHomeTemperatureFlow = flow {
        while (true) {
            val signal = awaitSensorSignal()
            emit(signal.temperatureCelsius)
            println("Emitted $signal")
        }
    }
        // Runs the upstream flow in Dispatchers.IO
        .flowOn(Dispatchers.IO)
        // Keeps the newest buffered value and drops older ones
        .conflate()
        // Collects the first two values from the upstream flow
        .take(2)
        .collect { temperature ->
            println("Received $temperature!")
            sendLatestTemperature(temperature)
        }
}
//sampleEnd
```
{kotlin-runnable="true"}

### Combining operators

Combining operators consume values from multiple upstream flows and return a single downstream flow.
Use them when collectors need values from more than one flow.

To pair values from two upstream flows, use the [`.zip()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/zip.html) operator.
It combines the first value from each flow, then the second value from each flow, and so on.
The resulting flow completes as soon as one of the upstream flows completes.

Here's an example:

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlin.random.Random
import kotlin.time.Duration.Companion.milliseconds
import kotlin.time.TimeSource

//sampleStart
suspend fun main() = withContext(Dispatchers.Default) {
    // Emits a ticker value every 100 milliseconds
    val tickerFlow = flow {
        while (true) {
            emit(Unit)
            delay(100.milliseconds)
        }
    }

    val start = TimeSource.Monotonic.markNow()
    tickerFlow
        // Combines each ticker emission with the next number
        .zip(flowOf(1, 2, 3)) { _, value ->
            value
        }.collect {
            println("${start.elapsedNow()}: received $it")
        }
}
//sampleEnd
```
{kotlin-runnable="true"}

To combine the latest value from multiple flows, use the [`.combine()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/combine.html) operator.
It emits a new value when any upstream flow emits a value, using the latest value from each upstream flow:

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlin.time.Duration.Companion.milliseconds
import kotlin.time.TimeSource

//sampleStart
enum class Theme {
    Dark,
    Light,
}

data class UiState(
    val messages: List<String>,
    val theme: Theme,
)

val messagesFlow = MutableStateFlow(
    listOf(
        "Hello!",
        "Is anyone here?",
    )
)

val themeFlow = MutableStateFlow(
    Theme.Light
)

// Combines the latest values from both upstream flows
val uiStateFlow = combine(messagesFlow, themeFlow) { messages, theme ->
    UiState(messages, theme)
}

suspend fun main() {
    withContext(Dispatchers.Default) {
        // Uses UNDISPATCHED to subscribe before the first update happens
        val uiUpdateJob = launch(start = CoroutineStart.UNDISPATCHED) {
            uiStateFlow.collect {
                // Draws the UI
                println(it)
            }
        }
        messagesFlow.update { messages -> messages + "I'll be back!" }
        delay(100.milliseconds)
        
        themeFlow.value = Theme.Dark
        delay(100.milliseconds)
        
        uiUpdateJob.cancel()
    }
}
//sampleEnd
```
{kotlin-runnable="true"}

In this example, `combine()` creates `uiStateFlow` from the latest values of `messagesFlow` and `themeFlow`.
Updating either upstream flow emits a new `UiState` with the latest messages and theme.

If you want to collect values from multiple flows concurrently and emit their values into one downstream flow, use the [`.merge()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/merge.html) operator:

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlin.time.Duration.Companion.milliseconds
import kotlin.time.TimeSource

//sampleStart
interface UiEvent

class ClickEvent: UiEvent

class RightClickEvent: UiEvent

suspend fun main() {
    withContext(Dispatchers.Default) {

        val clickFlow = MutableSharedFlow<ClickEvent>()
        val rightClickFlow = MutableSharedFlow<RightClickEvent>()

        coroutineScope {
            // Uses UNDISPATCHED to subscribe before the first update happens
            val collectJob = launch(start = CoroutineStart.UNDISPATCHED) {

                // Collects both upstream flows concurrently and emits their values downstream
                merge(clickFlow, rightClickFlow).collect {
                    println("Observed an event: $it")
                }
            }
            clickFlow.emit(ClickEvent())
            delay(100.milliseconds)
            
            clickFlow.emit(ClickEvent())
            delay(100.milliseconds)
            
            rightClickFlow.emit(RightClickEvent())
            delay(100.milliseconds)
            
            collectJob.cancel()
        }
    }
}
//sampleEnd
```
{kotlin-runnable="true"}

### Lifecycle operators

Lifecycle operators accept a suspending lambda that runs at a specific point during flow collection.
You can use them to place logic before the flow is collected, before each value is emitted,
after collection completes, or when the flow completes without emitting values.

The [`.onStart()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/on-start.html) operator runs its lambda before the upstream flow is collected.
For code that needs to run before each emitted value, use [`.onEach()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/on-each.html).

> Similarly to `.onStart()`, you can use [`.onSubscription()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/on-subscription.html) for hot flows to run code after a subscriber starts collecting the flow, but before it collects any emitted values.
>
{style="note"}

Here's an example that uses these operators to print a message before collection starts and before each value is emitted downstream:

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlin.time.Duration.Companion.milliseconds
import kotlin.time.TimeSource

// A simplified custom version of the default .onStart() operator
fun <T> Flow<T>.myOnStart(
    action: suspend FlowCollector<T>.() -> Unit
): Flow<T> = flow {
    this@flow.action()
    this@myOnStart.collect(this@flow)
}

suspend fun main() {
    withContext(Dispatchers.Default) {
        flowOf("Page 1", "Page 2", "Page 3").onStart {
            println("Processing pages!")
        }.onEach {
            println("Emitted $it")
        }.collect {
            println("Collected $it")
        }
    }
}
```
{kotlin-runnable="true"}

To run code after collection completes, use the [`.onCompletion()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/on-completion.html) operator.
Its lambda can emit values downstream when the upstream flow completes successfully, for example:

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlin.time.Duration.Companion.milliseconds
import kotlin.time.TimeSource

// A simplified custom version of the default .onCompletion() operator
fun <T> Flow<T>.myOnCompletion(
    action: suspend FlowCollector<T>.(cause: Throwable?) -> Unit
): Flow<T> = flow {
    var exception: Throwable? = null
    try {
        this@myOnCompletion.collect(this@flow)
    } catch (e: Throwable) {
        // Run `action`, but if `action` calls `emit`, throw `e` from it
        FlowCollector<T> { throw e }.action(e)
        throw e
    }
    this@flow.action(null)
}

//sampleStart
suspend fun main() {
    withContext(Dispatchers.Default) {
        flowOf("Page 1", "Page 2", "Page 3").onCompletion {
            println("Almost done...")
            // Emits an additional value after the upstream flow completes
            emit("Last Page!")
        }.collect {
            println("Collected $it")
        }
    }
}
//sampleEnd
```
{kotlin-runnable="true"}

To run code when the upstream flow completes without emitting any values, use the [`.onEmpty()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/on-empty.html) operator:

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlin.time.Duration.Companion.milliseconds
import kotlin.time.TimeSource

// A simplified custom version of the default .onEmpty() operator
fun <T> Flow<T>.myOnEmpty(
    action: suspend FlowCollector<T>.() -> Unit
): Flow<T> = flow {
    var emittedSomething = false
    this@myOnEmpty.collect { value ->
        emittedSomething = true
        this@flow.emit(value)
    }
    if (!emittedSomething) {
        action()
    }
}

//sampleStart
suspend fun main() {
    withContext(Dispatchers.Default) {
        flowOf("Page 1", "Page 2", "Page 3").onEmpty {
            // Doesn't print anything, because the upstream flow emits values
            println("No pages to load!")
        }.collect()
        flowOf<Int>().onEmpty {
            println("No pages to load!")
            // No pages to load!
        }.collect()
    }
}
//sampleEnd
```
{kotlin-runnable="true"}

## Terminal operators

Terminal operators collect a flow.
You can use them to consume emitted values, return a result based on the collected values, or [collect a flow in a specific `CoroutineScope`](#collect-a-flow-in-a-specific-coroutinescope).

To collect a flow, use the [`collect()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/collect.html) operator.
If you pass a lambda to `collect()`, it receives each emitted value:

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*

//sampleStart
suspend fun main() {
    withContext(Dispatchers.Default) {
        flowOf(1, 2, 3).collect {
            println("Collected $it!")
        }
    }
}
//sampleEnd
```
{kotlin-runnable="true"}

You can also call `collect()` without a lambda:

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*

//sampleStart
suspend fun main() {
    withContext(Dispatchers.Default) {
        flowOf(1, 2, 3).onEach {
            println("Collected $it!")
        }.collect()
    }
}
//sampleEnd
```
{kotlin-runnable="true"}

If you want to collect a flow but cancel unfinished work when a new value is emitted, use the [`collectLatest()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/collect-latest.html) operator:

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlin.time.Duration.Companion.milliseconds
import kotlin.time.TimeSource

//sampleStart
suspend fun main() {
    withContext(Dispatchers.Default) {
        flow {
            println("Emitting Page 1")
            emit("Page 1")
            delay(50.milliseconds)
            println("Emitting Page 2 in quick succession")
            emit("Page 2")
            delay(200.milliseconds)
            println("Emitting Page 3")
            emit("Page 3")
        }.flowOn(Dispatchers.IO).collectLatest {
            println("Starting to process $it!")
            try {
                delay(100.milliseconds)
            } catch (e: CancellationException) {
                println("Canceled processing $it.")
                throw e
            }
            println("Done processing!")
        }
    }
}
//sampleEnd
```
{kotlin-runnable="true"}

Some terminal operators collect a flow and return a result based on the collected values.
For example, you can use the [`.first()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/first.html) operator to return the first emitted value and then cancel collection:

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlin.time.Duration.Companion.milliseconds
import kotlin.time.TimeSource


suspend fun main() { 
    withContext(Dispatchers.Default) {
        val firstValue = flowOf(1, 2, 3).first()

        println(firstValue)
        // 1
    }
}
```
{kotlin-runnable="true"}

You can collect emitted values into a collection with the [`.toList()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/to-list.html) or [`.toSet()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/to-set.html) operators:

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*

// A simplified custom implementation of the default .toList() operator
suspend fun <T> Flow<T>.myToList(): List<T> = buildList {
    this@myToList.collect { value ->
        // Adds each emitted value to the resulting list
        add(value)
    }
}

//sampleStart
suspend fun main() {
    withContext(Dispatchers.Default) {
        val list = flowOf(1, 2, 3).toList()
        println(list)
        // [1, 2, 3]

        val set = flowOf(1, 2, 2, 3).toSet()
        println(set)
        // [1, 2, 3]
    }
}
//sampleEnd
```
{kotlin-runnable="true"}

To combine emitted values into a single result, use the [`.reduce()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/reduce.html) or [`.fold()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/fold.html) operators.
The `.fold()` operator uses the value you provide as its starting value, and the `.reduce()` operator uses the first emitted value instead.

Here's an example:

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*

//sampleStart
suspend fun main() {
    withContext(Dispatchers.Default) {
        // Uses the first emitted value as the starting value
        val reduced = flowOf(1, 2, 3).reduce { accumulator, value ->
            accumulator + value
        }

        // Starts with the provided starting value
        val folded = flowOf(1, 2, 3).fold(2) { accumulator, value ->
            accumulator + value
        }

        println(reduced)
        // 6

        println(folded)
        // 8
    }
}
//sampleEnd
```
{kotlin-runnable="true"}

### Collect a flow in a specific `CoroutineScope`

When a screen or another long-lived object needs values from a flow, start the collector in that object's `CoroutineScope`.
This ensures that canceling the object's `CoroutineScope` when the object is destroyed also cancels collection.

To collect a flow in a specific `CoroutineScope`, use the [`.launchIn()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/launch-in.html) terminal operator.
This operator returns the `Job` of the collecting coroutine.

Here's an example where a screen collects values from a `StateFlow` and stops the collecting coroutine when the screen closes:

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlin.time.Duration.Companion.milliseconds
import kotlin.time.TimeSource

// A simplified custom version of the default .launchIn() operator
fun <T> Flow<T>.myLaunchIn(scope: CoroutineScope): Job = scope.launch {
    this@myLaunchIn.collect()
}

//sampleStart
data class Coordinate(val x: Int, val y: Int)

class MyScreen(val scope: CoroutineScope) {
    private val _mousePosition =
        MutableStateFlow<Coordinate>(Coordinate(0, 0))
    val mousePosition get() = _mousePosition.asStateFlow()

    init {
        // Starts collecting the StateFlow in the screen's CoroutineScope
        mousePosition.onEach {
            updateStatusBar()
        }.launchIn(scope)
    }

    fun moveMouse(newCoordinate: Coordinate) {
        _mousePosition.value = newCoordinate
    }

    private fun updateStatusBar() {
        println("Mouse is at ${_mousePosition.value}")
    }
}

suspend fun main() {
    withContext(Dispatchers.Default) {
        val childScope = CoroutineScope(
            currentCoroutineContext() + Job(currentCoroutineContext()[Job])
        )
        val screen = MyScreen(childScope)
        delay(100.milliseconds)
        
        screen.moveMouse(Coordinate(10, 15))
        delay(100.milliseconds)
        
        screen.moveMouse(Coordinate(1, 3))
        delay(100.milliseconds)
        
        childScope.cancel()
    }
}
//sampleEnd
```
{kotlin-runnable="true"}
