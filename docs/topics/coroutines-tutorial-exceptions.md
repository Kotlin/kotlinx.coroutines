<contribute-url>https://github.com/Kotlin/kotlinx.coroutines/edit/master/docs/topics/</contribute-url>

[//]: # (title: Handle exceptions – tutorial)

<web-summary>The final part of the Kotlin coroutines and flows tutorial, where you learn how to handle exceptions in coroutines and flows.</web-summary>

The loading functions you've implemented so far assume that every HTTP request succeeds.

In this part of the tutorial, you'll request articles and comments from an unstable network and handle exceptions caused by unsuccessful responses.
You'll explore how exceptions propagate through a coroutine hierarchy and how to keep separate loading attempts independent.

## Handle exceptions in coroutines

To handle exceptions in coroutines, use `try` and `catch` blocks.
Place the code that might throw an exception in a `try` block and handle the exception in a `catch` block.

Here's an example using the application's custom `NetworkException`:

```kotlin
loadingScope.launch {
    val startTime = TimeSource.Monotonic.markNow()
    try {
        val articleResults = observeArticlesUnstable(service)
        updateResultsWithFailures(articleResults, startTime)
    } catch (e: NetworkException) {
        e.printStackTrace()
    }
}
```

In this example, `updateResultsWithFailures()` collects the flow returned by `observeArticlesUnstable()`.
If the flow throws a `NetworkException` during collection, the `catch` block handles it by printing its stack trace.

Additionally, you can use a `finally` block for cleanup code that runs after the `try` block and any `catch` block.
This cleanup runs whether the code in `try` completes normally, throws an exception, or stops because the coroutine is canceled.
For more information, see [The `finally` block](exceptions.md#the-finally-block).

### Exception propagation in coroutine hierarchies

With structured concurrency, coroutines form a hierarchy of parent and child coroutines.

If a child coroutine doesn't handle an exception, the exception propagates to its parent by default, unless it's a `CancellationException`.
This cancels the parent, which then cancels its other child coroutines.

Here's an example where an exception thrown in a child coroutine propagates to its parent:

```kotlin
loadingScope.launch { // Parent coroutine
    launch { // First child coroutine
        delay(1.seconds)
        // This message isn't printed because the parent coroutine cancels this child
        println("Coroutine completed")
    }

    launch { // Second child coroutine
        // The exception propagates to the parent coroutine and cancels it
        throw NetworkException("Loading articles was unsuccessful.")
    }
}
```

In this example, there is no `catch` block to handle the `NetworkException` thrown inside the child coroutine.
The exception propagates to the parent coroutine and cancels it.

Here's the same example with the exception handled inside the second child coroutine:

```kotlin
loadingScope.launch { // Parent coroutine
    launch { // First child coroutine
        delay(1.seconds)
        // This message is printed because the parent coroutine remains active
        println("Coroutine completed")
    }

    launch { // Second child coroutine
        try {
            throw NetworkException("Loading articles was unsuccessful.")
        } catch (e: NetworkException) {
            // The exception doesn't propagate to the parent coroutine
            e.printStackTrace()
        }
    }
}
```

In this example, the `catch` block handles the exception, so it doesn't propagate and the parent coroutine isn't canceled.

### Isolate failures with `SupervisorJob`

Child coroutines don't always represent work that should fail together.
When they represent independent operations, an exception in one child coroutine shouldn't cancel the parent or affect its other child coroutines.

You can use a [`SupervisorJob`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-supervisor-job.html) instead of a regular `Job` when child coroutines represent independent operations.
Unlike a `Job`, a `SupervisorJob` isn't canceled when one of its child coroutines fails.
Other child coroutines can continue running, and you can start new child coroutines in the same coroutine scope.

> Canceling the `SupervisorJob` cancels all its child coroutines.
> 
{style="note"}

### Observe a failed loading attempt

Open the `desktop-client/src/jvmMain/kotlin/org/example/articles/tasks/Task6Exceptions.kt` file.

This file declares the `ArticleResult` type, which represents the outcome of loading one article:

```kotlin
sealed interface ArticleResult {
    data class Success(val article: Article) : ArticleResult
    data class Failure(val articleInfo: ArticleInfo, val exception: Throwable) : ArticleResult
}
```

A `Success` object holds a loaded `Article` object.
A `Failure` object holds the article information and the exception that stopped the request.

The initial `observeArticlesUnstable()` function loads the comments for one article at a time and doesn't handle exceptions:

```kotlin
fun observeArticlesUnstable(service: BlogService): Flow<ArticleResult> = flow {
    val articleInfoList = service.getArticleInfoListUnstable()
    articleInfoList.forEach { articleInfo ->
        val comments = service.getCommentsUnstable(articleInfo)
        emit(ArticleResult.Success(Article(articleInfo, comments)))
    }
}
```

Run the application, select **UNSTABLE_NETWORK** from the **Loading Mode** menu, and click **Load comments**.

The first unsuccessful response throws a `NetworkException`, which stops the loading attempt. 
The application then displays **Loading status: failed** and **Loading failed: HTTP 500**.

The `loadingScope` property in the `desktop-client/src/jvmMain/kotlin/org/example/articles/ui/ArticlesViewModel.kt` file currently uses a regular `Job`:

```kotlin
private val loadingScope =
    CoroutineScope(Job(viewModelScope.coroutineContext.job) + Dispatchers.Main)
```

Each loading attempt runs in a coroutine whose `Job` is a child of this `Job`.
The exception from the loading coroutine propagates to this `Job` and cancels it.

If you click **Load comments** again, the application can't run another loading attempt because the `Job` is already canceled.

### Task – Implement independent loading attempts

Open the `desktop-client/src/jvmMain/kotlin/org/example/articles/ui/ArticlesViewModel.kt` file and find the `loadingScope` property:

```kotlin
private val loadingScope =
    CoroutineScope(Job(viewModelScope.coroutineContext.job) + Dispatchers.Main)
```

Update this property so that an exception from one loading attempt doesn't cancel `loadingScope` or prevent later attempts from running.
At the same time, ensure that canceling `viewModelScope` still cancels `loadingScope`.

#### Tip for independent loading attempts {initial-collapse-state="collapsed" collapsible="true" id="independent-loading-tip"}

Use a `SupervisorJob` with `viewModelScope.coroutineContext.job` as its parent.

#### Solution for independent loading attempts {initial-collapse-state="collapsed" collapsible="true" id="independent-loading-solution"}

Replace the regular `Job` with a `SupervisorJob`:

```kotlin
private val loadingScope =
    CoroutineScope(
        SupervisorJob(viewModelScope.coroutineContext.job) + Dispatchers.Main
    )
```

An exception from one loading attempt no longer cancels `loadingScope`, so the application can start another attempt.
If `viewModelScope` is canceled, cancellation still propagates to `loadingScope` and its child coroutines.

### Observe independent loading attempts

Run the application again, select **UNSTABLE_NETWORK**, and click **Load comments**.

The `observeArticlesUnstable()` function still doesn't handle exceptions, so an unsuccessful response fails the loading attempt.

[`CoroutineExceptionHandler`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-coroutine-exception-handler/)
handles exceptions that a coroutine can't propagate to a parent.
Here, the application passes a `CoroutineExceptionHandler` to `.launch()` because a `SupervisorJob` doesn't handle exceptions from its child coroutines.
The handler receives the `NetworkException` and updates the loading status.

However, the exception no longer cancels `loadingScope`.
If you click **Load comments** again, the application starts another loading attempt in a new coroutine.

## Load comments from an unstable network

The `desktop-client/src/jvmMain/kotlin/org/example/articles/network/BlogService.kt` file declares the `getArticleInfoListUnstable()`
and `getCommentsUnstable()` suspending functions for requesting data with simulated network failures:

```kotlin
override suspend fun getArticleInfoListUnstable(): List<ArticleInfo> {
    log("Started loading articles")
    val response = client.get(articlesUnstableEndpoint)
    response.throwIfUnsuccessful("Loaded articles failure: ${response.status}")
    return response.body<List<ArticleInfo>>()
        .also { 
            log("Loaded articles unstable") 
        }
}

override suspend fun getCommentsUnstable(articleInfo: ArticleInfo): List<Comment> {
    log("Started loading comments for article ${articleInfo.title}")
    val response = client.get(commentsUnstableEndpoint(articleInfo.id))
    response.throwIfUnsuccessful("Loaded comments failure for article ${articleInfo.title}: ${response.status}")
    return response.body<List<Comment>>()
        .also {
            log("Loaded comments unstable for article ${articleInfo.title}")
        }
}
```

Each function sends an HTTP request that has a 30% chance of returning an unsuccessful response.
When a response is unsuccessful, the shared `throwIfUnsuccessful()` function throws a `NetworkException`:

```kotlin
private fun HttpResponse.throwIfUnsuccessful(failureLog: String) {
    if (!status.isSuccess()) {
        log(failureLog)
        throw NetworkException("HTTP ${status.value}")
    }
}
```

The same file declares this exception type:

```kotlin
class NetworkException(message: String) : Exception(message)
```

The `getArticleInfoListUnstable()` call runs before any comment requests.
If it throws a `NetworkException`, the exception propagates from the flow and stops the loading attempt.
The initial `observeArticlesUnstable()` function also lets exceptions from individual comment requests propagate.
As a result, one unsuccessful comment response stops the loading attempt, even though the comments for the remaining articles could still load.

The comment requests are independent, so in the next task you'll handle each failure separately.

### Task – Implement article loading from an unstable network

Open the `desktop-client/src/jvmMain/kotlin/org/example/articles/tasks/Task6Exceptions.kt` file again.
It contains the following `observeArticlesUnstable()` function:

```kotlin
fun observeArticlesUnstable(service: BlogService): Flow<ArticleResult> = flow {
    val articleInfoList = service.getArticleInfoListUnstable()
    articleInfoList.forEach { articleInfo ->
        val comments = service.getCommentsUnstable(articleInfo)
        emit(ArticleResult.Success(Article(articleInfo, comments)))
    }
}
```

Update the function so that it:

* Requests the list of available articles with the `getArticleInfoListUnstable()` function.
* Starts a child coroutine for each `ArticleInfo` object.
* Loads the comments for the articles concurrently with the `getCommentsUnstable()` function.
* Sends an `ArticleResult.Success` object when the comments for an article have loaded.
* Sends an `ArticleResult.Failure` object when the request for an article's comments throws a `NetworkException`.

Keep the `getArticleInfoListUnstable()` call outside the `try` block so that any exception it throws propagates from the flow and stops the loading attempt.

#### Tip for article loading from an unstable network {initial-collapse-state="collapsed" collapsible="true" id="unstable-loading-tip"}

Adapt the `channelFlow()` structure of the `observeArticlesConcurrently()` function in the `Task5AsyncProgress.kt` file.
In each child coroutine, use a `try` block for the `getCommentsUnstable()` call and a `catch` block for the `NetworkException`:

```kotlin
launch {
    val result = try {
        /* Create an ArticleResult.Success object */
    } catch (exception: NetworkException) {
        /* Create an ArticleResult.Failure object */
    }
    send(result)
}
```

#### Solution for article loading from an unstable network {initial-collapse-state="collapsed" collapsible="true" id="unstable-loading-solution"}

1. Use the `channelFlow()` builder function to create the flow.
2. Call the `getArticleInfoListUnstable()` function and store the returned list.
3. Use a `.forEach()` function to process each `ArticleInfo` object.
4. For each object, call the `.launch()` coroutine builder function to start a child coroutine that loads its comments.
5. In each child coroutine:
    * Call the `getCommentsUnstable()` function in a `try` block and create an `ArticleResult.Success` object from the article information and comments.
    * Create an `ArticleResult.Failure` object from the article information and the exception in the `catch` block.
    * Use the `send()` function to send the result.

```kotlin
fun observeArticlesUnstable(service: BlogService): Flow<ArticleResult> = channelFlow {
    val articleInfoList = service.getArticleInfoListUnstable()
    articleInfoList.forEach { articleInfo ->
        launch {
            val result = try {
                ArticleResult.Success(Article(articleInfo, service.getCommentsUnstable(articleInfo)))
            } catch (exception: NetworkException) {
                ArticleResult.Failure(articleInfo, exception)
            }
            send(result)
        }
    }
}
```

The `catch` block handles the `NetworkException` inside the child coroutine, so the exception doesn't propagate to the `channelFlow()` block or affect the other child coroutines.
Because the `getArticleInfoListUnstable()` call is outside the try block,
an exception from this call propagates from the flow and stops the loading attempt.

### Observe loading from an unstable network

Run the application, select **UNSTABLE_NETWORK** from the **Loading Mode** menu, and click **Load comments**.

The application displays each successfully loaded article and lists failed comment requests in red.
A failed comment request doesn't stop the remaining requests, and the application displays **Loading status: completed with errors** when loading finishes.

![Article list after unstable-network requests fail, showing the loaded articles and the failed requests in red](unstable-network-failure.png){width="700"}

If you click **Load comments** again, the application can start a new loading attempt because the previous exception didn't cancel `loadingScope`.

The simulated failures are random, so a loading attempt can also complete without any failed requests.

### Test your implementation

Run the tests in the `desktop-client/src/jvmTest/kotlin/org/example/articles/tasks/Task6ExceptionsKtTest.kt` file.

The tests use the Turbine library to collect the flow and check that the `observeArticlesUnstable()` function:

* Sends an `ArticleResult.Success` object for each article whose comments load successfully.
* Sends an `ArticleResult.Failure` object with a `NetworkException` for each article whose comments fail to load.
* Completes after sending a result for every article.
* Completes within the expected concurrent loading time.
* Propagates a `NetworkException` when the request for the article list fails.

Instead of `MockBlogService`, the tests use `UnstableMockBlogService` to simulate failures for specific comment requests or the article-list request.
This makes the simulated failures predictable, so the tests can compare the results with the expected ones.

<list id="tour-nav">
  <li>
    <a as="button" href="coroutines-tutorial-channelflow.md" mode="outline" icon="arrow-left" icon-position="left">Previous step</a>
  </li>
</list>

## What's next

Congratulations on completing the coroutines and flows tutorial!

Along the way, you explored a wide range of coroutine concepts, from suspending functions and concurrent coroutines to structured concurrency, cancellation, flows, and exception propagation.
You applied these concepts to keep the application responsive, load comments concurrently, display results progressively, and handle unstable network requests.

If you have any questions or feedback about coroutines:

* **Kotlin Slack**: Get an [invite](https://surveys.jetbrains.com/s3/kotlin-slack-sign-up) and join the [#coroutines](https://kotlinlang.slack.com/archives/C1CFAFJSK) channel.
* **Kotlin issue tracker**: [Report a new issue](https://youtrack.jetbrains.com/newIssue?project=KT).

If you'd like to dive deeper into coroutines, explore these topics:

* [Coroutine basics](coroutines-basics.md)
* [Coroutine cancellation](coroutines-cancellation.md)
* [Flows](coroutines-flow.md)
