# kotlinx.coroutines 

Library support for Kotlin coroutines in
[Kotlin/JS](https://kotlinlang.org/docs/reference/js-overview.html).

```kotlin
suspend fun main() = coroutineScope {
    launch { 
       delay(1000)
       println("Kotlin Coroutines World!") 
    }
    println("Hello")
}
```

## Documentation 

* [Guide to kotlinx.coroutines by example on JVM](https://kotlinlang.org/docs/reference/coroutines/coroutines-guide.html) (**read it first**)
* [Full kotlinx.coroutines API reference](https://kotlin.github.io/kotlinx.coroutines)
