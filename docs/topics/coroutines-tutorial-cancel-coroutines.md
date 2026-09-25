<contribute-url>https://github.com/Kotlin/kotlinx.coroutines/edit/master/docs/topics/</contribute-url>

[//]: # (title: Cancel concurrent loading with structured concurrency – tutorial)

Concurrent loading starts several child coroutines to request comments.
When loading is no longer needed, the application must be able to stop these coroutines as a group.

In this part of the tutorial, you'll compare the cancellation behavior of child coroutines started in the scope created by `coroutineScope()` and coroutines started in `GlobalScope`.

## Cancel coroutines

Cancellation lets you request to stop a coroutine before it completes.

Cancellation works through a coroutine's `Job` handle, which represents the lifecycle of a coroutine and its parent-child relationships.
The `.launch()` coroutine builder function returns a `Job`.
The `.async()` coroutine builder function returns a `Deferred`, which implements `Job` and supports the same cancellation behavior.

You can request cancellation by invoking the [`cancel()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-job/cancel.html) function on a coroutine's `Job` handle.

In the Articles application, the `ArticlesViewModel.loadComments()` function stores the `Job` returned by `loadingScope.launch()` in the `loadingJob` property.
When you click **Cancel**, the `ArticlesViewModel.cancelLoading()` function invokes `cancel()` on this `Job`.

## Cancellation propagation

In the previous part of the tutorial, the `loadArticlesConcurrently()` function used `coroutineScope()` to connect each child coroutine to the parent loading coroutine.

Structured concurrency ensures that canceling a coroutine also cancels all its children.
This behavior is known as *cancellation propagation*.

In **CONCURRENT** mode, each `.async()` call starts a child coroutine that requests comments for an `ArticleInfo` object.
When the application cancels the parent loading coroutine, cancellation propagates to these child coroutines and stops their work as well.

### Suspension points and cancellation

In Kotlin, coroutine cancellation is _cooperative_.
Coroutines react to cancellation when they suspend or check for cancellation explicitly.

When a coroutine is canceled, it continues until it reaches a point where it may suspend, also known as a _suspension point_.
If the coroutine suspends there, the suspending function checks whether it has been canceled.
If it has, the coroutine stops and throws a `CancellationException`.

Each child coroutine in `loadArticlesConcurrently()` calls the suspending `getComments()` function.
The function can suspend while waiting for an HTTP response, giving the coroutine a suspension point where it can react to cancellation.

### Task — Implement a delay before requesting comments

Open the `desktop-client/src/jvmMain/kotlin/org/example/articles/tasks/Task2SequentialVsAsynchronous.kt` file.

The `loadArticlesConcurrently()` function calls `getComments()` as soon as each child coroutine starts.
Because all the child coroutines start quickly, the local server usually receives every HTTP request before you can click **Cancel**.

Canceling the parent coroutine still cancels its child coroutines, but it can't prevent HTTP requests that have already reached the server from completing.
As a result, the server can continue logging `GET` requests after you cancel loading.

To make cancellation easier to observe, use the [`delay()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/delay.html) suspending function before each child coroutine calls `getComments()`.
The `delay()` function accepts a `Duration` value.
To express this duration in seconds, import the `seconds` extension property from the `kotlin.time` package.

Here's an example:

```kotlin
import kotlinx.coroutines.delay
import kotlin.time.Duration.Companion.seconds

suspend fun waitBeforeRequest() {
    delay(3.seconds)
}
```

Now, add a three-second delay before each call to `getComments()` in the `loadArticlesConcurrently()` function.

#### Solution for delaying comment requests {initial-collapse-state="collapsed" collapsible="true" id="comment-request-delay-solution"}

1. Add the necessary imports for the `delay()` function and the `seconds` extension property.
2. In each `.async()` block, use `delay(3.seconds)` before calling `getComments()`.

```kotlin
import kotlinx.coroutines.delay
import kotlin.time.Duration.Companion.seconds

// Task: Implement concurrent loading of articles
suspend fun loadArticlesConcurrently(
    service: BlogService
): List<Article> = coroutineScope {
    service.getArticleInfoList()
        .map { articleInfo ->
            async {
                delay(3.seconds)
                Article(
                    articleInfo,
                    service.getComments(articleInfo)
                )
            }
        }
        .let { it.awaitAll() }
}
```

The `delay()` function suspends each child coroutine for three seconds before it calls `getComments()`.
This provides a suspension point where the child coroutine can react to cancellation before sending its HTTP request.

After implementing the next version that [starts coroutines in `GlobalScope`](#start-coroutines-in-globalscope), you'll compare how the two implementations react to cancellation.

### Start coroutines in `GlobalScope`

The [`GlobalScope`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-global-scope/) object provides a scope that isn't connected to the parent loading coroutine.

A coroutine started with `GlobalScope.async()` isn't a child of the loading coroutine.
Therefore, canceling the loading coroutine doesn't automatically cancel it.

The coroutine can still be canceled by invoking `cancel()` on its own `Deferred` handle.
However, this doesn't happen automatically through cancellation propagation.

> This task uses `GlobalScope` to demonstrate what happens when coroutines aren't connected through structured concurrency.
> In production applications, use `GlobalScope` only when the coroutines should remain active for the application's entire lifetime and you manage their cancellation explicitly.
>
{style="warning"}

### Task — Implement loading with `GlobalScope`

Open the `desktop-client/src/jvmMain/kotlin/org/example/articles/tasks/Task3StructuralConcurrency.kt` file.
It contains the `loadArticlesNonCancelable()` function with a `TODO()` placeholder:

```kotlin
// Run both versions and try to cancel
suspend fun loadArticlesNonCancelable(service: BlogService): List<Article> {
    TODO()
}
```

> The application invokes this function when you select **NON_CANCELABLE** from the **Loading Mode** menu.
> 
{style="tip"}

Implement the function by adapting the `loadArticlesConcurrently()` function from the previous task.
Start the coroutines that request comments in `GlobalScope` and return the resulting `Article` objects after all the coroutines complete.

Add the same three-second delay before each call to `getComments()`.
This ensures that the scope where each coroutine starts is the only difference between the two implementations.

#### Solution for loading with GlobalScope {initial-collapse-state="collapsed" collapsible="true" id="global-scope-loading-solution"}

1. Call the `getArticleInfoList()` function and store the returned list.
2. Use the `.map()` extension function to process each `ArticleInfo` object.
3. Inside `.map()`, call `GlobalScope.async()`:
    * Use `delay(3.seconds)` to suspend the coroutine before it sends the HTTP request.
    * Call the `getComments()` function.
    * Create an `Article` object from the article information and comments.
4. Call the `.awaitAll()` extension function on the resulting list and return the completed `Article` objects.

```kotlin
import kotlinx.coroutines.delay
import kotlin.time.Duration.Companion.seconds

suspend fun loadArticlesNonCancelable(
    service: BlogService
): List<Article> {
    val articleInfoList = service.getArticleInfoList()
    val deferreds = articleInfoList.map { article ->
        GlobalScope.async {
            delay(3.seconds)
            Article(article, service.getComments(article))
        }
    }
    return deferreds.awaitAll()
}
```

### Compare the cancellation behavior

First, run the application and select **CONCURRENT** from the **Loading Mode** menu.
Click **Load comments**, then click **Cancel** before loading finishes.

When you click **Cancel**, the `ArticlesViewModel.cancelLoading()` function in the `desktop-client/src/jvmMain/kotlin/org/example/articles/ui/ArticlesViewModel.kt` file invokes `cancel()` on `loadingJob`.
This property stores the `Job` returned by the `.launch()` call in `loadComments()`.

In **CONCURRENT** mode, cancellation propagates through the coroutine hierarchy to the child coroutines started inside the `loadArticlesConcurrently()` function.
As a result, child coroutines still suspended in `delay()` stop before calling `getComments()`, and the application doesn't request the remaining comments:

![Console output showing that structured child coroutines stop before sending comment requests](cancelable-scope.png){width="700"}

Next, select **NON_CANCELABLE**, click **Load comments**, and click **Cancel** again.

The application still cancels the parent loading coroutine.
However, the coroutines started with `GlobalScope.async()` aren't its children, so cancellation doesn't propagate to them.
They continue requesting comments after the parent loading coroutine has been canceled:

![Console output showing that coroutines started in GlobalScope continue sending comment requests after cancellation](globalscope-cancel.png){width="700"}

> You can still cancel coroutines started in `GlobalScope` by invoking `cancel()` on their `Deferred` handles.
> 
{style="tip"}

### Test your implementation

Run the tests in the `desktop-client/src/jvmTest/kotlin/org/example/articles/tasks/Task3StructuralConcurrencyKtTest.kt` file.

The tests check the following behavior:

* The `loadArticlesNonCancelable()` function returns the expected `Article` objects when loading completes.
* The `loadArticlesConcurrently()` function reacts to cancellation.
The test starts the function in a coroutine, waits for one second of virtual time, and cancels its `Job`.
It then checks that the `Job` is canceled and that cancellation completes before two seconds of virtual time have elapsed.

The tests don't check whether the coroutines started in `GlobalScope` continue after the parent loading coroutine is canceled.
You verified this behavior by comparing the two loading modes in the application.

In the next part of the tutorial, you'll use a flow to report loading progress as each article becomes available.

## Next step

<list columns="2" id="tour-nav">
  <li>
    <a as="button" href="coroutines-tutorial-concurrent-loading.md" mode="outline" icon="arrow-left" icon-position="left">Previous step</a>
  </li>
  <li>
    <a as="button" href="coroutines-tutorial-loading-progress-with-flow.md" mode="classic" icon="arrow-right" icon-position="right">Next step</a>
  </li>
</list>
