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

Implement the function by adapting the sequential loading logic from the suspending `loadArticles()` function in the `desktop-client/src/jvmMain/kotlin/org/example/articles/tasks/Task1BlockVsSuspend.kt` file.
Load the comments for one article at a time and emit each resulting `Article` object as soon as its comments have loaded.

#### Tip for progress reporting {initial-collapse-state="collapsed" collapsible="true" id="progress-reporting-tip"}

Call `service.getArticleInfoList()` and store the returned list in a variable named `list`.
Then use a `for` loop to adapt the `Article` construction from the suspending `loadArticles()` function:

```kotlin
val list = service.getArticleInfoList()
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

### Optional task — Create tests for sequential loading {initial-collapse-state="collapsed" collapsible="true" id="sequential-loading-tests-exercise"}

You can use the [Turbine library](https://github.com/cashapp/turbine) to test flows, including the values they emit and how they complete.

To collect a flow in a Turbine test, call the [`.test()`](https://cashapp.github.io/turbine/docs/1.x/-turbine/app.cash.turbine/test.html) extension function on it.
Inside the lambda passed to `.test()`, use:

* The [`awaitItem()`](https://cashapp.github.io/turbine/docs/1.x/-turbine/app.cash.turbine/await-item.html) function to suspend until the flow emits the next value and retrieve it.
* The [`awaitComplete()`](https://cashapp.github.io/turbine/docs/1.x/-turbine/app.cash.turbine/await-complete.html) function to verify that the flow completes successfully after emitting the expected values.

The `.test()` function is suspending.
To call it from a test, use the [`runTest()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-test/kotlinx.coroutines.test/run-test.html) function, which runs the test body in a coroutine.

Unlike `runBlocking()`, `runTest()` skips delays controlled by its test scheduler by advancing virtual time.
This allows the test to complete quickly while preserving the simulated loading duration.

For example, the following test verifies that a flow emits `1`, waits for one second using the `delay()` function, emits `2`, and completes successfully:

```kotlin
@Test
fun `test a delayed flow`() = runTest {
    flow {
        emit(1)
        delay(1.seconds)
        emit(2)
    }.test {
        assertEquals(1, awaitItem())
        assertEquals(2, awaitItem())
        awaitComplete()
    }
}
```

To measure how much virtual time passes while collecting a flow, use the [`currentTime`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-test/kotlinx.coroutines.test/current-time.html) property.
Inside a `runTest()` block, this property returns the current virtual time in milliseconds.

Store its value before collecting the flow, then subtract it from `currentTime` afterward.
Convert the result to a `Duration` with the `milliseconds` extension property from `kotlin.time.Duration.Companion`:

```kotlin
val startTime = currentTime

// Collect the flow

val totalTime = (currentTime - startTime).milliseconds
```

Open the `desktop-client/src/jvmTest/kotlin/org/example/articles/exercises/SequentialTest.kt` file.
It contains the following test functions with `TODO()` placeholders:

```kotlin
@OptIn(ExperimentalCoroutinesApi::class)
class SequentialTest {
    @Test
    fun `test observeArticlesLoading Result`() = runTest {
        TODO()
    }
    
    @Test
    fun `test observeArticlesLoading Duration`() = runTest {
        TODO()
    }
}
```

Implement the tests so that:

* The `test observeArticlesLoading Result()` function verifies that `observeArticlesLoading()` emits the expected Article objects in order.
* The `test observeArticlesLoading Duration()` function verifies that collecting the flow takes the expected amount of virtual time.

Pass the `MockBlogService` object to the `observeArticlesLoading()` function.
Use the following test data:

* `ArticlesFakeDataResults.expectedSequentialList.list` contains the expected `Article` objects.
* `ArticlesFakeDataResults.expectedSequentialList.duration` contains the expected loading duration.
* `ArticlesFakeData.getArticles().size` provides the number of values to retrieve from the flow.

#### Solution for sequential loading tests {initial-collapse-state="collapsed" collapsible="true" id="sequential-loading-tests-solution"}

For the `test observeArticlesLoading Result`() function:

1. Create a mutable list to store the emitted `Article` objects.
2. Call the `observeArticlesLoading()` function with `MockBlogService`, then call the `.test()` extension function on the returned flow.
3. Use the `repeat()` function with `ArticlesFakeData.getArticles().size`.
4. During each iteration, call the `awaitItem()` function and add the returned `Article` object to the mutable list.
5. Call the `awaitComplete()` function to verify that the flow completes successfully.
6. Use the `assertEquals()` function to compare the collected objects with `ArticlesFakeDataResults.expectedSequentialList.list`.

For the `test observeArticlesLoading Duration`() function:

1. Store the value of the `currentTime` property before collecting the flow.
2. Call the `observeArticlesLoading()` function with `MockBlogService`, then call the `.test()` extension function on the returned flow.
3. Use the `repeat()` function with `ArticlesFakeData.getArticles().size` and call the `awaitItem()` function during each iteration.
4. Call the `awaitComplete()` function to verify that the flow completes successfully.
5. Subtract the stored time from the current value of the `currentTime` property and convert the result to a `Duration`.
6. Use the `assertEquals()` function to compare the duration with `ArticlesFakeDataResults.expectedSequentialList.duration`.

```kotlin
import app.cash.turbine.test
import org.example.articles.data.ArticlesFakeDataResults
import org.example.articles.data.MockBlogService
import org.example.articles.model.Article
import org.example.articles.tasks.observeArticlesLoading
import org.example.data.ArticlesFakeData
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.test.currentTime
import kotlinx.coroutines.test.runTest
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.time.Duration.Companion.milliseconds

@OptIn(ExperimentalCoroutinesApi::class)
class SequentialTest {
    @Test
    fun `test observeArticlesLoading Result`() = runTest {
        val results = mutableListOf<Article>()
        observeArticlesLoading(MockBlogService).test {
            repeat(ArticlesFakeData.getArticles().size) {
                results += awaitItem()
            }
            awaitComplete()
        }
        assertEquals(
            expected = ArticlesFakeDataResults.expectedSequentialList.list,
            actual = results,
            message = "Wrong emission order/result for 'observeArticlesLoading' " +
                    "(loading is sequential, so articles should arrive in list order)"
        )
    }

    @Test
    fun `test observeArticlesLoading Duration`() = runTest {
        val startTime = currentTime
        observeArticlesLoading(MockBlogService).test {
            repeat(ArticlesFakeData.getArticles().size) { awaitItem() }
            awaitComplete()
        }
        val totalTime = (currentTime - startTime).milliseconds
        assertEquals(
            expected = ArticlesFakeDataResults.expectedSequentialList.duration,
            actual = totalTime,
            message = "Wrong total virtual time for 'observeArticlesLoading'"
        )
    }
}
```

### Test your implementation

If you completed the optional test-writing exercise, run the tests in the `desktop-client/src/jvmTest/kotlin/org/example/articles/exercises/SequentialTest.kt` file.
Otherwise, run the provided tests in the `desktop-client/src/jvmTest/kotlin/org/example/articles/tasks/Task4ProgressKtTest.kt` file.

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
    <a as="button" href="coroutines-tutorial-channelflow.md" mode="classic" icon="arrow-right" icon-position="right">Next step</a>
  </li>
</list>
