# Module kotlinx-coroutines-guava

Integration with Guava [ListenableFuture](https://github.com/google/guava/wiki/ListenableFutureExplained).

Coroutine builders:

| **Name** | **Result** | **Scope**  | **Description**
| -------- | ---------- | ---------- | ---------------
| [future] | [ListenableFuture][com.google.common.util.concurrent.ListenableFuture] | [CoroutineScope] | Returns a single value with the future result 

Extension functions:

| **Name** | **Description**
| -------- | ---------------
| [ListenableFuture.await][com.google.common.util.concurrent.ListenableFuture.await] | Awaits for completion of the future (cancellable)
| [Deferred.asListenableFuture][kotlinx.coroutines.Deferred.asListenableFuture] | Converts a deferred value to the future

## Example

Given the following functions defined in some Java API based on Guava:

```java
public ListenableFuture<Image> loadImageAsync(String name); // starts async image loading
public Image combineImages(Image image1, Image image2); // synchronously combines two images using some algorithm
```

We can consume this API from Kotlin coroutine to load two images and combine then asynchronously. 
The resulting function returns `ListenableFuture<Image>` for ease of use back from Guava-based Java code. 

```kotlin
fun combineImagesAsync(name1: String, name2: String): ListenableFuture<Image> = future {
    val future1 = loadImageAsync(name1) // start loading first image
    val future2 = loadImageAsync(name2) // start loading second image
    combineImages(future1.await(), future2.await()) // wait for both, combine, and return result
}
```

Note that this module should be used only for integration with existing Java APIs based on `ListenableFuture`. 
Writing pure-Kotlin code that uses `ListenableFuture` is highly not recommended, since the resulting APIs based
on the futures are quite error-prone. See the discussion on 
[Asynchronous Programming Styles](https://github.com/Kotlin/kotlin-coroutines/blob/master/kotlin-coroutines-informal.md#asynchronous-programming-styles)
for details on general problems pertaining to any future-based API and keep in mind that `ListenableFuture` exposes
a _blocking_ method 
[get](https://docs.oracle.com/javase/8/docs/api/java/util/concurrent/Future.html#get--) 
that makes it especially bad choice for coroutine-based Kotlin code.

# Package kotlinx.coroutines.future

Integration with Guava [ListenableFuture](https://github.com/google/guava/wiki/ListenableFutureExplained).

<!--- MODULE kotlinx-coroutines-core -->
<!--- INDEX kotlinx.coroutines -->

[CoroutineScope]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-coroutine-scope/index.html

<!--- MODULE kotlinx-coroutines-guava -->
<!--- INDEX kotlinx.coroutines.guava -->

[future]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-guava/kotlinx.coroutines.guava/future.html
[com.google.common.util.concurrent.ListenableFuture.await]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-guava/kotlinx.coroutines.guava/await.html
[kotlinx.coroutines.Deferred.asListenableFuture]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-guava/kotlinx.coroutines.guava/as-listenable-future.html

<!--- INDEX com.google.common.util.concurrent -->

[com.google.common.util.concurrent.ListenableFuture]: https://google.github.io/guava/releases/31.0.1-jre/api/docs/com/google/common/util/concurrent/ListenableFuture.html

<!--- END -->
