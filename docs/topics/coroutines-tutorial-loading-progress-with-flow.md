<contribute-url>https://github.com/Kotlin/kotlinx.coroutines/edit/master/docs/topics/</contribute-url> <show-structure depth="2"/>

[//]: # (title: Show loading progress with a flow – tutorial)

The loading functions you've implemented so far return the articles only after all their comments have loaded.

In this part of the tutorial, you'll use a [flow](coroutines-flow.md) to load each article's comments and produce the corresponding `Article` object.
This allows the application to display articles progressively instead of waiting for the complete list.

## Flows

A _flow_ represents a sequential stream of values that can be produced asynchronously.
Unlike a suspending function, which returns one value, a flow can produce multiple sequential values over time.

In a flow, the code that produces values is called the _emitter_, and the code that consumes them is called the _collector_.

The [`flow()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/flow.html) builder function creates a [_cold flow_](coroutines-flow.md#cold-flows).
A cold flow starts producing values only when a collector collects it.
Each collector starts a new, independent execution of the flow.

Inside a `flow()` block, use the [`emit()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/-flow-collector/emit.html) function to emit values:

```kotlin
fun messageFlow(): Flow<String> = flow {
    emit("Loading")
    emit("Finished")
}
```

> You can call suspending functions inside a `flow()` block.
> 
{style="tip"}

To collect the emitted values, use the `collect()` function.
The lambda passed to `collect()` receives each value:

```kotlin
suspend fun printMessages() {
    messageFlow().collect { message ->
        println(message)
    }
}
```

### Task — Implement progress reporting

Open the `desktop-client/src/jvmMain/kotlin/org/example/articles/tasks/Task4Progress.kt` file.
It contains the `observeArticlesLoading()` function with a `TODO()` placeholder:

```kotlin
// Task: Implement loading of articles and comments using flows (with progress!)
fun observeArticlesLoading(service: BlogService): Flow<Article> = flow {
    TODO()
}
```

Implement the function so that it loads the comments for one article at a time and emits each resulting `Article` object as soon as its comments have loaded.

#### Tip for progress reporting {initial-collapse-state="collapsed" collapsible="true" id="progress-reporting-tip"}

Call the `getArticleInfoList()` function to request the list of available articles.
Then use a `for` loop to load the comments for each article and emit the resulting `Article` object:

```kotlin
for (articleInfo in list) {
    emit(/* Create an Article object */)
}
```

#### Solution for progress reporting {initial-collapse-state="collapsed" collapsible="true" id="progress-reporting-solution"}

1. Call the `getArticleInfoList()` function and store the returned list.
2. Use a `for` loop to process each `ArticleInfo` object.
3. For each object:
    * Call the `getComments()` function.
    * Create an `Article` object from the article information and comments.
    * Use the `emit()` function to emit the `Article` object.

```kotlin
// Task: Implement loading of articles and comments using flows (with progress!)
fun observeArticlesLoading(service: BlogService): Flow<Article> = flow {
    val list = service.getArticleInfoList()
    for (articleInfo in list) {
        emit(Article(articleInfo, service.getComments(articleInfo)))
    }
}
```

The flow emits one `Article` object after each call to `getComments()` completes.
The collector receives the object immediately and updates the displayed results.

### Observe loading progress

Run the application, select **WITH_PROGRESS** from the **Loading Mode** menu, and click **Load comments**.

In this mode, the `ArticlesViewModel.loadComments()` function calls `observeArticlesLoading()` and passes the returned `Flow<Article>` to `updateResultsWithProgress()`:

```kotlin
WITH_PROGRESS -> {
    val articleFlow = observeArticlesLoading(service)
    updateResultsWithProgress(articleFlow, startTime)
}
```

The `observeArticlesLoading()` function returns a cold flow, so the application doesn't start loading articles until `updateResultsWithProgress()` collects it.

![Flow collection starts article loading and updates the displayed results](flow-tutorial-progress.svg){width="700"}

Once collection starts, the application requests comments sequentially, so loading all articles still takes approximately 10 seconds.
However, it adds each `Article` object to the displayed results as soon as the flow emits it.

![Partially loaded article list while loading is still in progress](load-progress.png){width="700"}

### Test your implementation

Run the tests in the `desktop-client/src/jvmTest/kotlin/org/example/articles/tasks/Task4ProgressKtTest.kt` file.

The tests use the [Turbine library](https://github.com/cashapp/turbine) to collect and check the flow's emissions.
They check that the `observeArticlesLoading()` function:

* Emits the expected `Article` objects in order.
* Completes after emitting all the objects.
* Uses the expected sequential loading time.

The tests use virtual time, so you don't have to wait for the simulated delays.

In the next part of the tutorial, you'll use `channelFlow()` to load comments concurrently and emit each `Article` object when it becomes available.

## Next step

<list columns="2" id="tour-nav">
  <li>
    <a as="button" href="coroutines-tutorial-cancel-coroutines.md" mode="outline" icon="arrow-left" icon-position="left">Previous step</a>
  </li>
  <li>
    <a as="button" href="concurrent-progress.md" mode="classic" icon="arrow-right" icon-position="right">Next step</a>
  </li>
</list>
