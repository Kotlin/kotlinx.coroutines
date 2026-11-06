<contribute-url>https://github.com/Kotlin/kotlinx.coroutines/edit/master/docs/topics/</contribute-url> <show-structure depth="2"/>

[//]: # (title: Emit values concurrently with channelFlow – tutorial)

In the previous part of the tutorial, you used a flow to display articles as their comments loaded.
However, the application still requested comments for one article at a time.

In this part, you'll use `channelFlow()` to load comments for articles concurrently.
This way, the application can display each resulting `Article` object as soon as its comments become available.

## Emit values concurrently with `channelFlow()`

The `flow()` builder function is simple and efficient for flows that emit values sequentially from a single coroutine.
To produce values from multiple coroutines concurrently, use the [`channelFlow()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/channel-flow.html) builder function.

Like `flow()`, `channelFlow()` creates a cold flow, but it uses a [_channel_](channels.md) to send values from multiple coroutines.
Its block provides a `CoroutineScope` for starting child coroutines and a [`SendChannel`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-send-channel/) for sending values from them.

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

### Task – Implement concurrent progress reporting

Open the `desktop-client/src/jvmMain/kotlin/org/example/articles/tasks/Task5AsyncProgress.kt` file.
It contains the `observeArticlesConcurrently()` function with a `TODO()` placeholder:

```kotlin
// Task: Implement concurrent loading of comments using flows
fun observeArticlesConcurrently(service: BlogService): Flow<Article> {
    TODO()
}
```

Implement the function so that it:

* Requests the list of available articles.
* Starts a child coroutine for each `ArticleInfo` object.
* Loads comments for the articles concurrently.
* Sends each resulting `Article` object when its comments have loaded.

#### Tip for concurrent progress reporting {initial-collapse-state="collapsed" collapsible="true" id="concurrent-progress-tip"}

Use the `channelFlow()` function to create the flow.
Inside its block, use a `for` loop to start a child coroutine for each `ArticleInfo` object:

```kotlin
for (articleInfo in list) {
    launch {
        send(/* Create an Article object */)
    }
}
```

Each child coroutine can call the suspending `getComments()` function and send the resulting `Article` object independently.

#### Solution for concurrent progress reporting {initial-collapse-state="collapsed" collapsible="true" id="concurrent-progress-solution"}

1. Use the `channelFlow()` builder function to create the flow.
2. Call the `getArticleInfoList()` function and store the returned list.
3. Use a `for` loop to process each `ArticleInfo` object.
4. For each object, call the `.launch()` coroutine builder function to start a child coroutine that loads its comments.
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
After the `getComments()` function returns the comments, the coroutine creates and sends the corresponding `Article` object.

### Observe concurrent progress

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
Because the comment requests take different amounts of time, the order of the displayed articles isn't guaranteed.

![Articles appearing progressively while channelFlow loads comments concurrently](concurrent-channelflow-loading.png){width="700"}

### Optional task – Create tests for concurrent loading {initial-collapse-state="collapsed" collapsible="true" id="concurrent-loading-tests-exercise"}

This exercise builds on the optional test-writing exercise from the [previous part](coroutines-tutorial-loading-progress-with-flow.md) of the tutorial.
Follow the same test structure as in the previous exercise, using `.test()`, `awaitItem()`, `awaitComplete()`, `runTest()`, and `currentTime`.

Unlike sequential loading, concurrent loading doesn't guarantee the order in which the flow emits its values.
To verify the results without requiring a particular order, convert the expected and collected lists to sets with the [`.toSet()`](https://kotlinlang.org/api/core/kotlin-stdlib/kotlin.collections/to-set.html) extension function before comparing them.

Like before, you can use the `currentTime` property to measure the elapsed virtual time.
Its value is in milliseconds, but `ArticlesFakeDataResults.expectedConcurrentList.duration` is a `Duration`.
To compare both values in milliseconds, use the [`inWholeMilliseconds`](https://kotlinlang.org/api/core/kotlin-stdlib/kotlin.time/-duration/in-whole-milliseconds.html) property.

To verify that the elapsed time doesn't exceed the expected upper bound, use the [`assertTrue()`](https://kotlinlang.org/api/core/kotlin-test/kotlin.test/assert-true.html) function.

Open the `desktop-client/src/jvmTest/kotlin/org/example/articles/exercises/AsyncProgressTurbineTest.kt` file.
It contains the following test functions with `TODO()` placeholders:

```kotlin
@OptIn(ExperimentalCoroutinesApi::class)
class AsyncProgressTurbineTest {
    @Test
    fun `test observeArticlesConcurrently Result`() = runTest {
        TODO()
    }

    @Test
    fun `test observeArticlesConcurrently Duration`() = runTest {
        TODO()
    }
}
```

Implement the tests so that:

* The `test observeArticlesConcurrently Result()` function verifies that `observeArticlesConcurrently()` emits all the expected `Article` objects, regardless of their order.
* The `test observeArticlesConcurrently Duration()` function verifies that collecting the flow completes within the expected concurrent loading time.

Pass the `MockBlogService` object to the `observeArticlesConcurrently()` function.
Use the following test data:

* `ArticlesFakeDataResults.expectedConcurrentList.list` contains the expected `Article` objects.
* `ArticlesFakeDataResults.expectedConcurrentList.duration` contains the upper bound for the loading duration.
* `ArticlesFakeData.getArticles().size` provides the number of values to retrieve from the flow.

#### Solution for concurrent loading tests {initial-collapse-state="collapsed" collapsible="true" id="concurrent-loading-tests-solution"}

For the `test observeArticlesConcurrently Result()` function:

1. Create a mutable list to store the emitted `Article` objects.
2. Call the `observeArticlesConcurrently()` function with `MockBlogService`, then call the `.test()` extension function on the returned flow.
3. Use the `repeat()` function with `ArticlesFakeData.getArticles().size`.
4. During each iteration, call the `awaitItem()` function and add the returned `Article` object to the mutable list.
5. Call the `awaitComplete()` function to verify that the flow completes successfully.
6. Convert the expected and collected lists to sets with the `.toSet()` extension function.
7. Use the `assertEquals()` function to compare the sets.

```kotlin
@Test
fun `test observeArticlesConcurrently Result`() = runTest {
    val results = mutableListOf<Article>()
    observeArticlesConcurrently(MockBlogService).test {
        repeat(ArticlesFakeData.getArticles().size) {
            results += awaitItem()
        }
        awaitComplete()
    }
    assertEquals(
        expected = ArticlesFakeDataResults.expectedConcurrentList.list.toSet(),
        actual = results.toSet(),
        message = "Wrong set of emitted articles for 'observeArticlesConcurrently' " +
                "(order isn't guaranteed when loading concurrently, but all articles should still arrive)"
    )
}
```

To implement the `test observeArticlesConcurrently Duration()` test:

1. Store the value of the `currentTime` property before collecting the flow.
2. Call the `observeArticlesConcurrently()` function with `MockBlogService`, then call the `.test()` extension function on the returned flow.
3. Use the `repeat()` function with `ArticlesFakeData.getArticles().size` and call the `awaitItem()` function during each iteration.
4. Call the `awaitComplete()` function to verify that the flow completes successfully.
5. Subtract the stored time from the current value of the `currentTime` property.
6. Convert `ArticlesFakeDataResults.expectedConcurrentList.duration` to milliseconds with its `inWholeMilliseconds` property.
7. Use the `assertTrue()` function to verify that the elapsed time doesn't exceed the expected upper bound.

```kotlin
@Test
fun `test observeArticlesConcurrently Duration`() = runTest {
    val startTime = currentTime
    observeArticlesConcurrently(MockBlogService).test {
        repeat(ArticlesFakeData.getArticles().size) { awaitItem() }
        awaitComplete()
    }
    val totalTime = currentTime - startTime
    val upperBound = ArticlesFakeDataResults.expectedConcurrentList.duration.inWholeMilliseconds
    assertTrue(
        totalTime <= upperBound,
        "Concurrent loading took $totalTime ms of virtual time, expected at most $upperBound ms"
    )
}
```

### Test your implementation

If you completed the optional test-writing exercise, run the tests in the `desktop-client/src/jvmTest/kotlin/org/example/articles/exercises/AsyncProgressTurbineTest.kt` file.
Otherwise, run the tests in the `desktop-client/src/jvmTest/kotlin/org/example/articles/tasks/Task5AsyncProgressKtTest.kt` file.

The tests use the Turbine library to collect the flow and check that the `observeArticlesConcurrently()` function:

* Sends all the expected `Article` objects, regardless of their order.
* Completes after sending all the objects.
* Completes within the expected concurrent loading time.

The result test compares sets instead of lists because concurrent loading doesn't guarantee the order of the emitted objects.

In the next part of the tutorial, you'll handle exceptions when comment requests fail because of an unstable network.

## Next step

<list columns="2" id="tour-nav">
  <li>
    <a as="button" href="coroutines-tutorial-loading-progress-with-flow.md" mode="outline" icon="arrow-left" icon-position="left">Previous step</a>
  </li>
  <li>
    <a as="button" href="coroutines-tutorial-exceptions.md" mode="classic" icon="arrow-right" icon-position="right">Next step</a>
  </li>
</list>