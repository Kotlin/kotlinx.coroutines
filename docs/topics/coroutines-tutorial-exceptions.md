<contribute-url>https://github.com/Kotlin/kotlinx.coroutines/edit/master/docs/topics/</contribute-url>

[//]: # (title: Handle exceptions – tutorial)

The loading functions you've implemented so far assume that every HTTP request succeeds.

In this part of the tutorial, you'll request comments from an unstable network and handle exceptions caused by unsuccessful responses.
You'll explore how exceptions propagate through a coroutine hierarchy and how to keep separate loading attempts independent.

## Exception propagation in coroutine hierarchies

With structured concurrency, coroutines form a hierarchy of parent and child coroutines.

If a child coroutine fails with an exception other than `CancellationException`, it cancels its parent with that exception.
The parent then cancels its other child coroutines.

### Isolate failures with `SupervisorJob`

Child coroutines don't always represent work that should fail together.
When they represent independent operations, an exception in one child coroutine shouldn't cancel the parent or affect its other child coroutines.

You can use a [`SupervisorJob`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-supervisor-job.html) instead of a regular `Job` when child coroutines represent independent operations.
Unlike a `Job`, a `SupervisorJob` isn't canceled when one of its child coroutines fails.
Other child coroutines can continue running, and you can start new child coroutines in the same coroutine scope.

> Canceling the `SupervisorJob` cancels all its child coroutines.
> 
{style="tip"}

### Observe a failed loading attempt

Open the `desktop-client/src/jvmMain/kotlin/org/example/articles/tasks/Task6Exceptions.kt` file.

The initial `observeArticlesUnstable()` function throws a `NetworkException` when the application collects its flow:

```kotlin
fun observeArticlesUnstable(service: BlogService): Flow<Article> = flow {
    throw NetworkException("Loading articles was unsuccessful.")
}
```

Run the application, select **UNSTABLE_NETWORK** from the **Loading Mode** menu, and click **Load comments**.

The exception stops the loading attempt, and the application displays **Loading status: failed**.

The `loadingScope` property in the `desktop-client/src/jvmMain/kotlin/org/example/articles/ui/ArticlesViewModel.kt` file currently uses a regular `Job`:

```kotlin
private val loadingScope =
    CoroutineScope(Job(viewModelScope.coroutineContext.job) + Dispatchers.Main)
```

Each loading attempt runs in a coroutine whose `Job` is a child of this `Job`.
The exception from the loading coroutine propagates to this `Job` and cancels it.

If you click **Load comments** again, the application can't run another loading attempt because the `Job` is already canceled.

### Task — Implement independent loading attempts

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

The `observeArticlesUnstable()` function still throws a `NetworkException`, so the loading attempt fails.
The `CoroutineExceptionHandler` passed to `.launch()` receives the exception and updates the loading status.

However, the exception no longer cancels `loadingScope`.
If you click **Load comments** again, the application starts another loading attempt in a new coroutine.

## Load comments from an unstable network

The initial `observeArticlesUnstable()` function deliberately throws a `NetworkException` before requesting any data.
This makes the effect of a failed loading attempt easy to observe.

Now, replace the deliberate exception with the article-loading logic.
The `desktop-client/src/jvmMain/kotlin/org/example/articles/network/BlogService.kt` file declares the `getCommentsUnstable()` suspending function for requesting comments with simulated network failures:

```kotlin
override suspend fun getCommentsUnstable(articleInfo: ArticleInfo): List<Comment> {
    log("Started loading comments for article ${articleInfo.title}")
    val response = client.get(commentsUnstableEndpoint(articleInfo.id))
    if (!response.status.isSuccess()) {
        log("Loaded comments failure for article ${articleInfo.title}: ${response.status}")
        throw NetworkException("Loading article ${articleInfo.id} was unsuccessful.")
    }
    return response.body<List<Comment>>()
        .also {
            log("Loaded comments unstable for article ${articleInfo.title}")
        }
}
```

The function sends an HTTP request with a 30% chance of receiving an unsuccessful response.
When the response is unsuccessful, the function throws a `NetworkException`:

```kotlin
class NetworkException(message: String) : Exception(message)
```

### Task — Implement article loading from an unstable network

Open the `desktop-client/src/jvmMain/kotlin/org/example/articles/tasks/Task6Exceptions.kt` file again.
It contains the following `observeArticlesUnstable()` function:

```kotlin
fun observeArticlesUnstable(service: BlogService): Flow<Article> = flow {
    throw NetworkException("Loading articles was unsuccessful.")
}
```

Replace the deliberately thrown `NetworkException` with code that:

* Requests the list of available articles.
* Loads the comments for one article at a time with the `getCommentsUnstable()` function.
* Emits each resulting `Article` object after its comments have loaded.

#### Tip for article loading from an unstable network {initial-collapse-state="collapsed" collapsible="true" id="unstable-loading-tip"}

Adapt the sequential flow structure of the `observeArticlesLoading()` function in the `Task4Progress.kt` file.

#### Solution for article loading from an unstable network {initial-collapse-state="collapsed" collapsible="true" id="unstable-loading-solution"}

1. Call the `getArticleInfoList()` function and store the returned list.
2. Use a `for` loop to process each `ArticleInfo` object.
3. For each object:
    * Call the `getCommentsUnstable()` function.
    * Create an `Article` object from the article information and comments.
    * Use the `emit()` function to emit the `Article` object.

```kotlin
import org.example.articles.model.Article
import org.example.articles.network.BlogService
import kotlinx.coroutines.flow.*

// Task: Implement loading of articles from an unstable network
fun observeArticlesUnstable(service: BlogService): Flow<Article> = flow {
    val list = service.getArticleInfoList()
    for (articleInfo in list) {
        emit(Article(articleInfo, service.getCommentsUnstable(articleInfo)))
    }
}
```

If `getCommentsUnstable()` returns the comments, the flow emits the corresponding `Article` object.
If the function throws a `NetworkException`, the exception stops the flow and propagates to the loading coroutine.

### Observe loading from an unstable network

Run the application, select **UNSTABLE_NETWORK** from the **Loading Mode** menu, and click **Load comments**.

The application displays each `Article` object emitted before an exception occurs.
If the `getCommentsUnstable()` function throws a `NetworkException`, the current loading attempt stops and the application displays the **FAILED** status.

![Article list after an unstable-network request fails, showing five loaded articles and a failed status](unstable-network-failure.png){width="700"}

If you click **Load comments** again, the application can start a new loading attempt because the previous exception didn't cancel `loadingScope`.

The simulated failures are random, so a loading attempt can also complete successfully.

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
