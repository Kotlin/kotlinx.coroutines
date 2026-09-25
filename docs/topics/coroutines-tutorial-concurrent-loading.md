<contribute-url>https://github.com/Kotlin/kotlinx.coroutines/edit/master/docs/topics/</contribute-url>

[//]: # (title: Concurrent loading – tutorial)

Coroutines can run concurrently with other coroutines and potentially in parallel.
In this part of the tutorial, you'll use multiple coroutines to request comments concurrently and reduce the total loading time.

## Concurrent coroutines

Two operations run concurrently when one can start before the other has finished.
On the JVM, coroutines can run concurrently on the same thread.
When a coroutine suspends, it stops using the thread until it can continue, allowing another coroutine to run on that thread.

As a result, concurrent operations don't require a separate thread for every coroutine.

To load comments concurrently, the implementation you'll write starts a separate coroutine for each `ArticleInfo` object returned by the `getArticleInfoList()` function.
Each coroutine calls the `getComments(articleInfo)` function to request that article's comments.
When one coroutine suspends while waiting for a response, the UI thread can run another coroutine and send the next HTTP request.

This allows multiple HTTP requests to remain in progress at the same time, even though the coroutines execute one at a time on the UI thread.

## Coroutine scopes and structured concurrency

When you start multiple coroutines, you need a way to manage them as a group.
The principle of _structured concurrency_ provides this structure by connecting each child coroutine to the scope in which you start it.

You can use the [`coroutineScope()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/coroutine-scope.html) coroutine builder function to create a `CoroutineScope`.
This function takes a suspending lambda and uses the created `CoroutineScope` as the [lambda's receiver](lambdas.md#function-literals-with-receiver).
This receiver provides the scope for child coroutines started in the lambda.

For example, the following function calls the `.launch()` coroutine builder function on this scope to start two child coroutines:

```kotlin
suspend fun printMessages() = coroutineScope {
    launch {
        println("Hello")
    }

    launch {
        println("World")
    }
}
```

Each `.launch()` call starts a child coroutine in the scope created by `coroutineScope()`.
The `printMessages()` function returns after both child coroutines complete.

## Return values from coroutines

In addition to the `.launch()` coroutine builder function, you can also use the [`.async()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/async.html) function to start a coroutine.

Both functions are extension functions on `CoroutineScope`.
When you call either function in a `coroutineScope()` block, it starts a child coroutine in that scope.

You can use these coroutine builder functions for different purposes:

* Use `.launch()` when the coroutine doesn't need to produce a result. It returns a [`Job`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-job/) handle that represents the coroutine.
* Use `.async()` when the coroutine needs to produce a result. It returns a [`Deferred`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-deferred/) handle that represents a result that becomes available when the coroutine completes.

To retrieve a result of an `.async()` function, use the [`await()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/await.html) function.
If the result isn't available yet, the `await()` function suspends until the coroutine completes and then returns the result:

```kotlin
suspend fun calculateAnswer(): Int = coroutineScope {
    val deferredAnswer: Deferred<Int> = async {
        6 * 7
    }

    deferredAnswer.await()
}
```

You can also retrieve results from multiple `Deferred` with the [`.awaitAll()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/await-all.html) extension function.
The `.awaitAll()` function suspends until all the coroutines complete and returns their results as a list.

Here's an example:

```kotlin
suspend fun calculateAnswers(): List<Int> = coroutineScope {
    val deferredAnswers: List<Deferred<Int>> = listOf(
        async { 6 * 7 },
        async { 7 * 8 }
    )

    deferredAnswers.awaitAll()
}
```

### Task — Implement concurrent loading

Open the `desktop-client/src/jvmMain/kotlin/org/example/articles/tasks/Task2SequentialVsAsynchronous.kt` file.

It contains the `loadArticlesConcurrently()` function with a `TODO()` placeholder:

```kotlin
// Task: Implement concurrent loading of articles
suspend fun loadArticlesConcurrently(service: BlogService): List<Article> = coroutineScope {
    TODO()
}
```

Implement the function by adapting the suspending `loadArticles()` function from the `Task1BlockVsSuspend.kt` file.
Load the comments for different `ArticleInfo` objects concurrently and return the resulting `Article` objects after all HTTP requests have completed.

#### Tip for concurrent loading {initial-collapse-state="collapsed" collapsible="true" id="concurrent-loading-tip"}

The `loadArticlesConcurrently()` function already creates a `CoroutineScope` with the `coroutineScope()` function.
Copy the loading logic from the suspending `loadArticles()` function into its block, then use `.async()` to start a child coroutine for each `ArticleInfo` object.

Base your solution on the following structure:

```kotlin
val deferredArticles: List<Deferred<Article>> = articleInfoList.map { article ->
    async {
        // Request the comments and create an Article object
    }
}
deferredArticles.awaitAll() // List<Article>
```

#### Solution for concurrent loading {initial-collapse-state="collapsed" collapsible="true" id="concurrent-loading-solution"}

Here's an example solution:

1. Call the `getArticleInfoList()` function to request the available `ArticleInfo` objects.
2. Use the `.map()` extension function to transform each `ArticleInfo` object into a `Deferred<Article>` handle:
    * Call the `.async()` function to start a child coroutine.
    * In the coroutine, call the `getComments()` function and create an `Article` object from the article information and comments.
3. Use the [`.let()`](https://kotlinlang.org/api/core/kotlin-stdlib/kotlin/let.html) extension function to call `.awaitAll()` on the resulting list of `Deferred<Article>` handles.
4. Return the `List<Article>` produced by `.awaitAll()` after all the child coroutines complete.

```kotlin
suspend fun loadArticlesConcurrently(service: BlogService): List<Article> = coroutineScope {
    service.getArticleInfoList()
        .map { article ->
            async {
                Article(
                    article,
                    service.getComments(article)
                )
            }
        }
        .let { it.awaitAll() }
}
```

### Observe concurrent loading

Run the application, select **CONCURRENT** from the **Loading Mode** menu, and click **Load comments**.

The application sends each HTTP request without waiting for the previous response.
While one coroutine waits for a response, another coroutine can call the `getComments()` function for another `ArticleInfo` object.

Loading now takes approximately 2 seconds instead of 10 seconds.
The requests remain in progress concurrently, so the longest simulated delay determines the total loading time instead of the sum of all delays.

![Concurrent loading](concurrent-loading.png){width="700"}

### Test your implementation

Run the tests in the `desktop-client/src/jvmTest/kotlin/org/example/articles/tasks/Task2SequentialVsAsynchronousKtTest.kt` file.

The tests check that the `loadArticlesConcurrently()` function returns the expected `Article` objects.
They also check that loading takes 2 seconds of virtual time, which matches the longest possible simulated delay.

In the next part of the tutorial, you'll explore how structured concurrency keeps concurrent loading cancelable.

## Next step

<list columns="2" id="tour-nav">
  <li>
    <a as="button" href="coroutines-tutorial-blocking-requests.md" mode="outline" icon="arrow-left" icon-position="left">Previous step</a>
  </li>
  <li>
    <a as="button" href="coroutines-tutorial-cancel-coroutines.md" mode="classic" icon="arrow-right" icon-position="right">Next step</a>
  </li>
</list>

