# Module kotlinx-coroutines-jdk8

Additional libraries for JDK8 (or Android API level 24).

Coroutine builders:

| **Name** | **Result** | **Scope**  | **Description**
| -------- | ---------- | ---------- | ---------------
| [future] | [CompletableFuture][java.util.concurrent.CompletableFuture] | [CoroutineScope] | Returns a single value with the future result 

Extension functions:

| **Name** | **Description**
| -------- | ---------------
| [CompletionStage.await][java.util.concurrent.CompletionStage.await] | Awaits for completion of the completion stage (non-cancellable)
| [CompletableFuture.await][java.util.concurrent.CompletableFuture.await] | Awaits for completion of the future (cancellable)
| [Deferred.asCompletableFuture][kotlinx.coroutines.experimental.Deferred.asCompletableFuture] | Converts a deferred value to the future

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

Note, that this module should be used only for integration with existing Java APIs based on `CompletableFuture`. 
Writing pure-Kotlin code that uses `CompletableFuture` is highly not recommended, since the resulting APIs based
on the futures are quite error-prone. See the discussion on 
[Asynchronous Programming Styles](https://github.com/Kotlin/kotlin-coroutines/blob/master/kotlin-coroutines-informal.md#asynchronous-programming-styles)
for details on general problems pertaining to any future-based API and keep in mind that `CompletableFuture` exposes
a _blocking_ method 
[get](https://docs.oracle.com/javase/8/docs/api/java/util/concurrent/Future.html#get--) 
that makes it especially bad choice for coroutine-based Kotlin code.

# Package kotlinx.coroutines.experimental.future

Additional libraries for JDK8 [CompletableFuture][java.util.concurrent.CompletableFuture].

<!--- SITE_ROOT https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core -->
<!--- DOCS_ROOT kotlinx-coroutines-core/target/dokka/kotlinx-coroutines-core -->
<!--- INDEX kotlinx.coroutines.experimental -->
[CoroutineScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-coroutine-scope/index.html
<!--- SITE_ROOT https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-jdk8 -->
<!--- DOCS_ROOT integration/kotlinx-coroutines-jdk8/target/dokka/kotlinx-coroutines-jdk8 -->
<!--- INDEX kotlinx.coroutines.experimental.future -->
[future]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-jdk8/kotlinx.coroutines.experimental.future/future.html
[java.util.concurrent.CompletableFuture]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-jdk8/kotlinx.coroutines.experimental.future/java.util.concurrent.-completable-future/index.html
[java.util.concurrent.CompletionStage.await]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-jdk8/kotlinx.coroutines.experimental.future/java.util.concurrent.-completion-stage/await.html
[java.util.concurrent.CompletableFuture.await]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-jdk8/kotlinx.coroutines.experimental.future/java.util.concurrent.-completable-future/await.html
[kotlinx.coroutines.experimental.Deferred.asCompletableFuture]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-jdk8/kotlinx.coroutines.experimental.future/kotlinx.coroutines.experimental.-deferred/as-completable-future.html
<!--- END -->
