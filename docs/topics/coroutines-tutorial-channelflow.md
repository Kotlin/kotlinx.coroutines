<contribute-url>https://github.com/Kotlin/kotlinx.coroutines/edit/master/docs/topics/</contribute-url> <show-structure depth="2"/>

[//]: # (title: Emit concurrent results with channelFlow – tutorial)

In this part of the tutorial, you'll use `channelFlow()` to load comments for several articles concurrently and report each `Article` object when its comments become available.

## Emit values concurrently with `channelFlow()`

The `flow()` builder function is simple and efficient for flows that emit values from one coroutine.
To produce values from multiple coroutines concurrently, use the [`channelFlow()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/channel-flow.html) builder function.

Like `flow()`, `channelFlow()` creates a cold flow.
However, its block provides a `CoroutineScope` for starting child coroutines and a `SendChannel` for sending values from them.

Inside a `channelFlow()` block:

* Use the `.launch()` coroutine builder function to start child coroutines.
* Use the [`send()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-send-channel/send.html) function instead of `emit()` to produce values.

For example, the following function starts two child coroutines that send values to the same flow:

```kotlin
fun messageFlow(): Flow<String> = channelFlow {
    launch {
        send("Hello")
    }

    launch {
        send("World")
    }
}
```

Because the child coroutines run concurrently, the order in which the collector receives their values isn't guaranteed.

## Task — Implement concurrent progress reporting

Open the `desktop-client/src/jvmMain/kotlin/org/example/articles/tasks/Task5AsyncProgress.kt` file.
It contains the `observeArticlesConcurrently()` function with a `TODO()` placeholder:

```kotlin
// Task: Implement concurrent loading of comments using flows
fun observeArticlesConcurrently(service: BlogService): Flow<Article> {
    TODO()
}
```

The application invokes this function when you select **CONCURRENT_WITH_PROGRESS** from the **Loading Mode** menu.

Implement the function so that it:

* Requests the list of available articles.
* Starts a child coroutine for each `ArticleInfo` object.
* Loads comments for the articles concurrently.
* Sends each resulting `Article` object when its comments have loaded.

### Tip for concurrent progress reporting {initial-collapse-state="collapsed" collapsible="true" id="concurrent-progress-tip"}

Use `channelFlow()` to create the flow.
Inside its block, use a `for` loop to start a child coroutine for each `ArticleInfo` object:

```kotlin
for (articleInfo in list) {
    launch {
        send(/* Create an Article object */)
    }
}
```

Each child coroutine can call the suspending `getComments()` function and send the resulting `Article` object independently.

### Solution for concurrent progress reporting {initial-collapse-state="collapsed" collapsible="true" id="concurrent-progress-solution"}

1. Use the `channelFlow()` builder function to create the flow.
2. Call the `getArticleInfoList()` function and store the returned list.
3. Use a `for` loop to process each `ArticleInfo` object.
4. For each object, call the `.launch()` coroutine builder function to start a child coroutine.
5. In each child coroutine:

    * Call the `getComments()` function.
    * Create an `Article` object from the article information and comments.
    * Use the `send()` function to send the `Article` object.

```kotlin
// Task: Implement concurrent loading of comments using flows
fun observeArticlesConcurrently(service: BlogService): Flow<Article> = channelFlow {
    val list = service.getArticleInfoList()
    for (articleInfo in list) {
        launch {
            send(Article(articleInfo, service.getComments(articleInfo)))
        }
    }
}
```

Each `.launch()` call starts a child coroutine that requests comments for one article.
When the comments arrive, the coroutine creates and sends the corresponding `Article` object.

## Observe concurrent progress

Run the application, select **CONCURRENT_WITH_PROGRESS** from the **Loading Mode** menu, and click **Load comments**.

In this mode, the `ArticlesViewModel.loadComments()` function calls `observeArticlesConcurrently()` and passes the returned `Flow<Article>` to `updateResultsWithProgress()`:

```kotlin
CONCURRENT_WITH_PROGRESS -> {
    val articleFlow = observeArticlesConcurrently(service)
    updateResultsWithProgress(articleFlow, startTime)
}
```

The `updateResultsWithProgress()` function collects the flow, which starts the `channelFlow()` block and its child coroutines.

The child coroutines request comments concurrently and send each `Article` object when its comments become available.
The application updates the displayed article list after receiving each object.

Loading takes approximately 2 seconds, and the articles appear progressively.
Because the comments requests take different amounts of time, the order of the displayed articles isn't guaranteed.

## Test your implementation

Run the tests in the `desktop-client/src/jvmTest/kotlin/org/example/articles/tasks/Task5AsyncProgressKtTest.kt` file.

The tests use the Turbine library to collect the flow and check that the `observeArticlesConcurrently()` function:

* Sends all the expected `Article` objects, regardless of their order.
* Completes after sending all the objects.
* Completes within the expected concurrent loading time.

The result test compares sets instead of lists because concurrent loading doesn't guarantee the order of the emitted objects.
The tests use virtual time, so you don't have to wait for the simulated delays.

In the next part of the tutorial, you'll handle failures while loading comments from an unstable network.

## Next step

<list columns="2" id="tour-nav">
  <li>
    <a as="button" href="loading-progress.md" mode="outline" icon="arrow-left" icon-position="left">Previous step</a>
  </li>
  <li>
    <a as="button" href="flow-failures.md" mode="classic" icon="arrow-right" icon-position="right">Next step</a>
  </li>
</list>
