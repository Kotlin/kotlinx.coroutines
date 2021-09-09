# Module kotlinx-coroutines-jdk8

Integration with JDK8 [CompletableFuture] (Android API level 24).

Coroutine builders:

| **Name** | **Result**          | **Scope**        | **Description**
| -------- | ------------------- | ---------------- | ---------------
| [future] | [CompletableFuture] | [CoroutineScope] | Returns a single value with the future result 

Extension functions:

| **Name** | **Description**
| -------- | ---------------
| [CompletionStage.await][java.util.concurrent.CompletionStage.await] | Awaits for completion of the completion stage
| [CompletionStage.asDeferred][java.util.concurrent.CompletionStage.asDeferred] | Converts completion stage to an instance of [Deferred]
| [Deferred.asCompletableFuture][kotlinx.coroutines.Deferred.asCompletableFuture] | Converts a deferred value to the future

## Example

Given the following functions defined in some Java API:

```java
public CompletableFuture<Image> loadImageAsync(String name); // starts async image loading
public Image combineImages(Image image1, Image image2); // synchronously combines two images using some algorithm
```

We can consume this API from Kotlin coroutine to load two images and combine then asynchronously. 
The resulting function returns `CompletableFuture<Image>` for ease of use back from Java. 

```kotlin
fun combineImagesAsync(name1: String, name2: String): CompletableFuture<Image> = future {
    val future1 = loadImageAsync(name1) // start loading first image
    val future2 = loadImageAsync(name2) // start loading second image
    combineImages(future1.await(), future2.await()) // wait for both, combine, and return result
}
```

Note that this module should be used only for integration with existing Java APIs based on `CompletableFuture`. 
Writing pure-Kotlin code that uses `CompletableFuture` is highly not recommended, since the resulting APIs based
on the futures are quite error-prone. See the discussion on 
[Asynchronous Programming Styles](https://github.com/Kotlin/KEEP/blob/master/proposals/coroutines.md#asynchronous-programming-styles)
for details on general problems pertaining to any future-based API and keep in mind that `CompletableFuture` exposes
a _blocking_ method 
[get](https://docs.oracle.com/javase/8/docs/api/java/util/concurrent/Future.html#get--) 
that makes it especially bad choice for coroutine-based Kotlin code.

# Package kotlinx.coroutines.future

Integration with JDK8 [CompletableFuture] (Android API level 24).

[CompletableFuture]: https://docs.oracle.com/javase/8/docs/api/java/util/concurrent/CompletableFuture.html

<!--- MODULE kotlinx-coroutines-core -->
<!--- INDEX kotlinx.coroutines -->

[CoroutineScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-coroutine-scope/index.html
[Deferred]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-deferred/index.html

<!--- MODULE kotlinx-coroutines-jdk8 -->
<!--- INDEX kotlinx.coroutines.future -->

[future]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-jdk8/kotlinx.coroutines.future/future.html
[java.util.concurrent.CompletionStage.await]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-jdk8/kotlinx.coroutines.future/await.html
[java.util.concurrent.CompletionStage.asDeferred]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-jdk8/kotlinx.coroutines.future/as-deferred.html
[kotlinx.coroutines.Deferred.asCompletableFuture]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-jdk8/kotlinx.coroutines.future/as-completable-future.html

<!--- END -->
