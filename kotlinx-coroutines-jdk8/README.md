# Module kotlinx-coroutines-jdk8

Additional libraries for JDK8 (or Android API level 24).

Coroutine builders:

| **Name** | **Result** | **Scope**  | **Description**
| -------- | ---------- | ---------- | ---------------
| [future] | [CompletableFuture][java.util.concurrent.CompletableFuture] | [CoroutineScope] | Returns a single value with the future result 

Extension functions:

| **Name** | **Description**
| -------- | ---------------
| [CompletableFuture.await][java.util.concurrent.CompletableFuture.await] | Awaits for completion of the future
| [Deferred.toCompletableFuture][kotlinx.coroutines.experimental.Deferred.toCompletableFuture] | Converts a deferred value to the future

# Package kotlinx.coroutines.experimental.future

Additional libraries for JDK8 [CompletableFuture][java.util.concurrent.CompletableFuture].

<!--- SITE_ROOT https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core -->
<!--- DOCS_ROOT kotlinx-coroutines-core/target/dokka/kotlinx-coroutines-core -->
<!--- INDEX kotlinx.coroutines.experimental -->
[CoroutineScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-coroutine-scope/index.html
<!--- SITE_ROOT https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-jdk8 -->
<!--- DOCS_ROOT kotlinx-coroutines-jdk8/target/dokka/kotlinx-coroutines-jdk8 -->
<!--- INDEX kotlinx.coroutines.experimental.future -->
[future]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-jdk8/kotlinx.coroutines.experimental.future/future.html
[java.util.concurrent.CompletableFuture]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-jdk8/kotlinx.coroutines.experimental.future/java.util.concurrent.-completable-future/index.html
[java.util.concurrent.CompletableFuture.await]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-jdk8/kotlinx.coroutines.experimental.future/await.html
[kotlinx.coroutines.experimental.Deferred.toCompletableFuture]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-jdk8/kotlinx.coroutines.experimental.future/to-completable-future.html
<!--- END -->
