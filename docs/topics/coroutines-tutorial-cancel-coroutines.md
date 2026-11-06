<contribute-url>https://github.com/Kotlin/kotlinx.coroutines/edit/master/docs/topics/</contribute-url>

[//]: # (title: Cancel concurrent loading with structured concurrency – tutorial)

Concurrent loading starts several child coroutines to request comments.
When loading is no longer needed, the application must be able to stop these coroutines as a group.
For example, a user may close a window, navigate away from a screen, or decide to cancel a long-running loading operation before it finishes.
In each case, the application can stop the remaining work instead of letting it continue in the background.

In this part of the tutorial, you'll explore the cancellation behavior of coroutines.

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
This behavior is known as _cancellation propagation_.

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

### Start coroutines in `GlobalScope`

The [`GlobalScope`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-global-scope/) object provides a scope that isn't connected to the parent loading coroutine.

A coroutine started with `GlobalScope.async()` isn't a child of the loading coroutine.
Therefore, canceling the loading coroutine doesn't automatically cancel it.

The coroutine can still be canceled by invoking `cancel()` on its own `Deferred` handle.
However, this doesn't happen automatically through cancellation propagation because starting the coroutine in `GlobalScope` breaks structured concurrency.

> `GlobalScope` is a delicate API, so avoid using it in production applications.
> This task uses `GlobalScope` to demonstrate the risks of running coroutines that aren't connected through structured concurrency.
> 
> One of its few legitimate use cases is for work that must remain active for the application's entire lifetime.
> Even then, a dedicated `CoroutineScope` tied to the application's lifecycle is a better solution that
> lets you manage application-wide coroutines as a group.
>
{style="warning"}

### Task – Implement loading with `GlobalScope`

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

#### Solution for loading with `GlobalScope` {initial-collapse-state="collapsed" collapsible="true" id="global-scope-loading-solution"}

1. Call the `getArticleInfoList()` function and store the returned list.
2. Use the `.map()` extension function to process each `ArticleInfo` object.
3. Inside `.map()`, call `GlobalScope.async()`:
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
As a result, the child coroutines stop their remaining work:

![Console output showing that structured child coroutines stop before sending comment requests](cancelable-scope.png){width="700"}

Next, select **NON_CANCELABLE**, click **Load comments**, and click **Cancel** again.

The application still cancels the parent loading coroutine.
However, the coroutines started with `GlobalScope.async()` aren't its children, so cancellation doesn't propagate to them.
They continue requesting comments after the parent loading coroutine has been canceled:

![Console output showing that coroutines started in GlobalScope continue sending comment requests after cancellation](globalscope-cancel.png){width="700"}

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
