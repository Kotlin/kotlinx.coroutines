# kotlinx.coroutines core tutorial

This is a DRAFT of a very short tutorial on core features of `kotlinx.coroutines`.

## Your first coroutine

Run the following code:

```kotlin
fun main(args: Array<String>) {
    launch(Here) { // create new coroutine without an explicit threading policy
        delay(1000L) // non-blocking delay for 1 second
        println("World!") // print after delay
    }
    println("Hello,") // main function continues while coroutine is delayed
}
```

> You can get full code with imports [here](src/test/kotlin/examples/tutorial-example-1.kt)

Run this code:

```
Hello!
World!
```

Essentially, coroutines are light-weight threads. You can achieve the same result replacing
`launch(Here) { ... }` with `thread { ... }` and `delay(...)` with `Thread.sleep(...)`. Try it.

If you start by replacing `launch(Here)` by `thread`, the compiler produces the following error:

```
Error: Kotlin: Suspend functions are only allowed to be called from a coroutine or another suspend function
```

That is because `delay` is a special _suspending function_ that does not block a thread, but _suspends_
coroutine and it can be only used from a coroutine.

## Coroutines ARE light-weight

Run the following code:

```kotlin
fun main(args: Array<String>) {
    repeat(100_000) {
        launch(Here) { // create new coroutine without an explicit threading policy
            delay(1000L) // non-blocking delay for 1 second
            print(".") // print one dot per coroutine
        }
    }
}
```

> You can get full code with imports [here](src/test/kotlin/examples/tutorial-example-2.kt)

It starts 100K coroutines and, after a second, each coroutine prints a dot. 
Now, try that with threads. What would happen? (Most likely your code will produce some sort of out-of-memory error)
