<!--- TEST_NAME SelectGuideTest --> 

**Table of contents**

<!--- TOC -->

* [Select Expression (experimental)](#select-expression-experimental)
  * [Selecting from channels](#selecting-from-channels)
  * [Selecting on close](#selecting-on-close)
  * [Selecting to send](#selecting-to-send)
  * [Selecting deferred values](#selecting-deferred-values)
  * [Switch over a channel of deferred values](#switch-over-a-channel-of-deferred-values)

<!--- END -->

## Select Expression (experimental)

Select expression makes it possible to await multiple suspending functions simultaneously and _select_
the first one that becomes available.

> Select expressions are an experimental feature of `kotlinx.coroutines`. Their API is expected to 
evolve in the upcoming updates of the `kotlinx.coroutines` library with potentially
breaking changes.

### Selecting from channels

Let us have two producers of strings: `fizz` and `buzz`. The `fizz` produces "Fizz" string every 300 ms:

<div class="sample" markdown="1" theme="idea" data-highlight-only>

```kotlin
fun CoroutineScope.fizz() = produce<String> {
    while (true) { // sends "Fizz" every 300 ms
        delay(300)
        send("Fizz")
    }
}
```

</div>

And the `buzz` produces "Buzz!" string every 500 ms:

<div class="sample" markdown="1" theme="idea" data-highlight-only>

```kotlin
fun CoroutineScope.buzz() = produce<String> {
    while (true) { // sends "Buzz!" every 500 ms
        delay(500)
        send("Buzz!")
    }
}
```

</div>

Using [receive][ReceiveChannel.receive] suspending function we can receive _either_ from one channel or the
other. But [select] expression allows us to receive from _both_ simultaneously using its
[onReceive][ReceiveChannel.onReceive] clauses:

<div class="sample" markdown="1" theme="idea" data-highlight-only>

```kotlin
suspend fun selectFizzBuzz(fizz: ReceiveChannel<String>, buzz: ReceiveChannel<String>) {
    select<Unit> { // <Unit> means that this select expression does not produce any result 
        fizz.onReceive { value ->  // this is the first select clause
            println("fizz -> '$value'")
        }
        buzz.onReceive { value ->  // this is the second select clause
            println("buzz -> '$value'")
        }
    }
}
```

</div>

Let us run it all seven times:

<!--- CLEAR -->

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.selects.*

fun CoroutineScope.fizz() = produce<String> {
    while (true) { // sends "Fizz" every 300 ms
        delay(300)
        send("Fizz")
    }
}

fun CoroutineScope.buzz() = produce<String> {
    while (true) { // sends "Buzz!" every 500 ms
        delay(500)
        send("Buzz!")
    }
}

suspend fun selectFizzBuzz(fizz: ReceiveChannel<String>, buzz: ReceiveChannel<String>) {
    select<Unit> { // <Unit> means that this select expression does not produce any result 
        fizz.onReceive { value ->  // this is the first select clause
            println("fizz -> '$value'")
        }
        buzz.onReceive { value ->  // this is the second select clause
            println("buzz -> '$value'")
        }
    }
}

fun main() = runBlocking<Unit> {
//sampleStart
    val fizz = fizz()
    val buzz = buzz()
    repeat(7) {
        selectFizzBuzz(fizz, buzz)
    }
    coroutineContext.cancelChildren() // cancel fizz & buzz coroutines
//sampleEnd        
}
```

</div>

> You can get the full code [here](../kotlinx-coroutines-core/jvm/test/guide/example-select-01.kt).

The result of this code is: 

```text
fizz -> 'Fizz'
buzz -> 'Buzz!'
fizz -> 'Fizz'
fizz -> 'Fizz'
buzz -> 'Buzz!'
fizz -> 'Fizz'
buzz -> 'Buzz!'
```

<!--- TEST -->

### Selecting on close

The [onReceive][ReceiveChannel.onReceive] clause in `select` fails when the channel is closed causing the corresponding
`select` to throw an exception. We can use [onReceiveOrNull][onReceiveOrNull] clause to perform a
specific action when the channel is closed. The following example also shows that `select` is an expression that returns 
the result of its selected clause:

<div class="sample" markdown="1" theme="idea" data-highlight-only>

```kotlin
suspend fun selectAorB(a: ReceiveChannel<String>, b: ReceiveChannel<String>): String =
    select<String> {
        a.onReceiveOrNull { value -> 
            if (value == null) 
                "Channel 'a' is closed" 
            else 
                "a -> '$value'"
        }
        b.onReceiveOrNull { value -> 
            if (value == null) 
                "Channel 'b' is closed"
            else    
                "b -> '$value'"
        }
    }
```

</div>

Note that [onReceiveOrNull][onReceiveOrNull] is an extension function defined only 
for channels with non-nullable elements so that there is no accidental confusion between a closed channel
and a null value. 

Let's use it with channel `a` that produces "Hello" string four times and 
channel `b` that produces "World" four times:

<!--- CLEAR -->

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.selects.*

suspend fun selectAorB(a: ReceiveChannel<String>, b: ReceiveChannel<String>): String =
    select<String> {
        a.onReceiveOrNull { value -> 
            if (value == null) 
                "Channel 'a' is closed" 
            else 
                "a -> '$value'"
        }
        b.onReceiveOrNull { value -> 
            if (value == null) 
                "Channel 'b' is closed"
            else    
                "b -> '$value'"
        }
    }
    
fun main() = runBlocking<Unit> {
//sampleStart
    val a = produce<String> {
        repeat(4) { send("Hello $it") }
    }
    val b = produce<String> {
        repeat(4) { send("World $it") }
    }
    repeat(8) { // print first eight results
        println(selectAorB(a, b))
    }
    coroutineContext.cancelChildren()  
//sampleEnd      
}    
```

</div>

> You can get the full code [here](../kotlinx-coroutines-core/jvm/test/guide/example-select-02.kt).

The result of this code is quite interesting, so we'll analyze it in more detail:

```text
a -> 'Hello 0'
a -> 'Hello 1'
b -> 'World 0'
a -> 'Hello 2'
a -> 'Hello 3'
b -> 'World 1'
Channel 'a' is closed
Channel 'a' is closed
```

<!--- TEST -->

There are couple of observations to make out of it. 

First of all, `select` is _biased_ to the first clause. When several clauses are selectable at the same time, 
the first one among them gets selected. Here, both channels are constantly producing strings, so `a` channel,
being the first clause in select, wins. However, because we are using unbuffered channel, the `a` gets suspended from
time to time on its [send][SendChannel.send] invocation and gives a chance for `b` to send, too.

The second observation, is that [onReceiveOrNull][onReceiveOrNull] gets immediately selected when the 
channel is already closed.

### Selecting to send

Select expression has [onSend][SendChannel.onSend] clause that can be used for a great good in combination 
with a biased nature of selection.

Let us write an example of producer of integers that sends its values to a `side` channel when 
the consumers on its primary channel cannot keep up with it:

<div class="sample" markdown="1" theme="idea" data-highlight-only>

```kotlin
fun CoroutineScope.produceNumbers(side: SendChannel<Int>) = produce<Int> {
    for (num in 1..10) { // produce 10 numbers from 1 to 10
        delay(100) // every 100 ms
        select<Unit> {
            onSend(num) {} // Send to the primary channel
            side.onSend(num) {} // or to the side channel     
        }
    }
}
```

</div>

Consumer is going to be quite slow, taking 250 ms to process each number:

<!--- CLEAR -->

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.selects.*

fun CoroutineScope.produceNumbers(side: SendChannel<Int>) = produce<Int> {
    for (num in 1..10) { // produce 10 numbers from 1 to 10
        delay(100) // every 100 ms
        select<Unit> {
            onSend(num) {} // Send to the primary channel
            side.onSend(num) {} // or to the side channel     
        }
    }
}

fun main() = runBlocking<Unit> {
//sampleStart
    val side = Channel<Int>() // allocate side channel
    launch { // this is a very fast consumer for the side channel
        side.consumeEach { println("Side channel has $it") }
    }
    produceNumbers(side).consumeEach { 
        println("Consuming $it")
        delay(250) // let us digest the consumed number properly, do not hurry
    }
    println("Done consuming")
    coroutineContext.cancelChildren()  
//sampleEnd      
}
```

</div> 
 
> You can get the full code [here](../kotlinx-coroutines-core/jvm/test/guide/example-select-03.kt).
  
So let us see what happens:
 
```text
Consuming 1
Side channel has 2
Side channel has 3
Consuming 4
Side channel has 5
Side channel has 6
Consuming 7
Side channel has 8
Side channel has 9
Consuming 10
Done consuming
```

<!--- TEST -->

### Selecting deferred values

Deferred values can be selected using [onAwait][Deferred.onAwait] clause. 
Let us start with an async function that returns a deferred string value after 
a random delay:

<div class="sample" markdown="1" theme="idea" data-highlight-only>

```kotlin
fun CoroutineScope.asyncString(time: Int) = async {
    delay(time.toLong())
    "Waited for $time ms"
}
```

</div>

Let us start a dozen of them with a random delay.

<div class="sample" markdown="1" theme="idea" data-highlight-only>

```kotlin
fun CoroutineScope.asyncStringsList(): List<Deferred<String>> {
    val random = Random(3)
    return List(12) { asyncString(random.nextInt(1000)) }
}
```

</div>

Now the main function awaits for the first of them to complete and counts the number of deferred values
that are still active. Note that we've used here the fact that `select` expression is a Kotlin DSL, 
so we can provide clauses for it using an arbitrary code. In this case we iterate over a list
of deferred values to provide `onAwait` clause for each deferred value.

<!--- CLEAR -->

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.selects.*
import java.util.*
    
fun CoroutineScope.asyncString(time: Int) = async {
    delay(time.toLong())
    "Waited for $time ms"
}

fun CoroutineScope.asyncStringsList(): List<Deferred<String>> {
    val random = Random(3)
    return List(12) { asyncString(random.nextInt(1000)) }
}

fun main() = runBlocking<Unit> {
//sampleStart
    val list = asyncStringsList()
    val result = select<String> {
        list.withIndex().forEach { (index, deferred) ->
            deferred.onAwait { answer ->
                "Deferred $index produced answer '$answer'"
            }
        }
    }
    println(result)
    val countActive = list.count { it.isActive }
    println("$countActive coroutines are still active")
//sampleEnd
}
```

</div>

> You can get the full code [here](../kotlinx-coroutines-core/jvm/test/guide/example-select-04.kt).

The output is:

```text
Deferred 4 produced answer 'Waited for 128 ms'
11 coroutines are still active
```

<!--- TEST -->

### Switch over a channel of deferred values

Let us write a channel producer function that consumes a channel of deferred string values, waits for each received
deferred value, but only until the next deferred value comes over or the channel is closed. This example puts together 
[onReceiveOrNull][onReceiveOrNull] and [onAwait][Deferred.onAwait] clauses in the same `select`:

<div class="sample" markdown="1" theme="idea" data-highlight-only>

```kotlin
fun CoroutineScope.switchMapDeferreds(input: ReceiveChannel<Deferred<String>>) = produce<String> {
    var current = input.receive() // start with first received deferred value
    while (isActive) { // loop while not cancelled/closed
        val next = select<Deferred<String>?> { // return next deferred value from this select or null
            input.onReceiveOrNull { update ->
                update // replaces next value to wait
            }
            current.onAwait { value ->  
                send(value) // send value that current deferred has produced
                input.receiveOrNull() // and use the next deferred from the input channel
            }
        }
        if (next == null) {
            println("Channel was closed")
            break // out of loop
        } else {
            current = next
        }
    }
}
```

</div>

To test it, we'll use a simple async function that resolves to a specified string after a specified time:


<div class="sample" markdown="1" theme="idea" data-highlight-only>

```kotlin
fun CoroutineScope.asyncString(str: String, time: Long) = async {
    delay(time)
    str
}
```

</div>

The main function just launches a coroutine to print results of `switchMapDeferreds` and sends some test
data to it:

<!--- CLEAR -->

<div class="sample" markdown="1" theme="idea" data-min-compiler-version="1.3">

```kotlin
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.selects.*
    
fun CoroutineScope.switchMapDeferreds(input: ReceiveChannel<Deferred<String>>) = produce<String> {
    var current = input.receive() // start with first received deferred value
    while (isActive) { // loop while not cancelled/closed
        val next = select<Deferred<String>?> { // return next deferred value from this select or null
            input.onReceiveOrNull { update ->
                update // replaces next value to wait
            }
            current.onAwait { value ->  
                send(value) // send value that current deferred has produced
                input.receiveOrNull() // and use the next deferred from the input channel
            }
        }
        if (next == null) {
            println("Channel was closed")
            break // out of loop
        } else {
            current = next
        }
    }
}

fun CoroutineScope.asyncString(str: String, time: Long) = async {
    delay(time)
    str
}

fun main() = runBlocking<Unit> {
//sampleStart
    val chan = Channel<Deferred<String>>() // the channel for test
    launch { // launch printing coroutine
        for (s in switchMapDeferreds(chan)) 
            println(s) // print each received string
    }
    chan.send(asyncString("BEGIN", 100))
    delay(200) // enough time for "BEGIN" to be produced
    chan.send(asyncString("Slow", 500))
    delay(100) // not enough time to produce slow
    chan.send(asyncString("Replace", 100))
    delay(500) // give it time before the last one
    chan.send(asyncString("END", 500))
    delay(1000) // give it time to process
    chan.close() // close the channel ... 
    delay(500) // and wait some time to let it finish
//sampleEnd
}
```

</div>

> You can get the full code [here](../kotlinx-coroutines-core/jvm/test/guide/example-select-05.kt).

The result of this code:

```text
BEGIN
Replace
END
Channel was closed
```

<!--- TEST -->

<!--- MODULE kotlinx-coroutines-core -->
<!--- INDEX kotlinx.coroutines -->

[Deferred.onAwait]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-deferred/on-await.html

<!--- INDEX kotlinx.coroutines.channels -->

[ReceiveChannel.receive]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-receive-channel/receive.html
[ReceiveChannel.onReceive]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-receive-channel/on-receive.html
[onReceiveOrNull]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/on-receive-or-null.html
[SendChannel.send]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-send-channel/send.html
[SendChannel.onSend]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-send-channel/on-send.html

<!--- INDEX kotlinx.coroutines.selects -->

[select]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.selects/select.html

<!--- END -->
