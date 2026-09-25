<contribute-url>https://github.com/Kotlin/kotlinx.coroutines/edit/master/docs/topics/</contribute-url>
<show-structure depth="2"/>

[//]: # (title: Replace blocking calls with suspending functions – tutorial)

In this part of the tutorial, you'll implement two strategies for loading articles and their comments.
First, you'll send requests synchronously from the thread that updates the interface and handles user input, also known as the _UI thread_.

You'll observe how blocking this thread affects the application.
Then, you'll send the same requests with suspending functions so that the application remains responsive while waiting for data.

## Explore the article-loading task

Open the `desktop-client/src/jvmMain/kotlin/org/example/articles/tasks/Task1BlockVsSuspend.kt` file.
It contains two `loadArticles()` functions with `TODO()` placeholders:

```kotlin
fun loadArticles(serviceBlocking: BlogServiceBlocking): List<Article> {
    TODO()
}

suspend fun loadArticles(service: BlogService): List<Article> {
    TODO()
}
```

The application invokes the corresponding function based on the selected loading mode:

* **BLOCKING** invokes the function with a `BlogServiceBlocking` parameter.
* **SUSPENDING** invokes the suspending function with a `BlogService` parameter.

> The file also contains the `main0()` and `main()` functions.
> You don't need to run these functions during the tutorial.
> [Run the **Articles** application](coroutines-and-flows-tutorial.md#run-the-application) instead.
>
{style="note"}

The two `loadArticles()` functions create and return instances of the `Article` data class.
Each instance combines an instance of the `ArticleInfo` data class with a list of instances of the `Comment` data class.
These data classes are declared in the following files:

* The `shared/src/main/kotlin/org/example/blog/ArticleInfo.kt` file contains:
    * `ArticleInfo`, which stores an article's ID, author, and title.
    * `Comment`, which stores a comment's author and content.
* The `desktop-client/src/jvmMain/kotlin/org/example/articles/model/Article.kt` file contains the `Article` data class, which combines an `ArticleInfo` object with its comments: `Article(info: ArticleInfo, comments: List<Comment>)`.

The project provides two ways to request data from the local server:

* The `BlogServiceBlocking` class in the `network/BlogServiceBlocking.kt` file uses the [Retrofit library](https://github.com/lysine-dev/retrofit) to send blocking HTTP requests.
* The `BlogService` interface in the `network/BlogService.kt` file declares suspending functions for the same requests.
  Its private `BlogServiceImpl` class implements these functions with [Ktor](https://ktor.io/docs/welcome.html).

For this task, you'll use the following functions from the `BlogServiceBlocking` class and the `BlogService` interface:

* The `getArticleInfoList()` function to request the list of available articles.
* The `getComments(articleInfo: ArticleInfo)` function to request the comments for the specified `ArticleInfo`.

The local server applies a predefined delay of 0.25 to 2 seconds before returning the comments for each article.
In both implementations for this task, the application loads comments for one article at a time.
As a result, these delays can add up to approximately 10 seconds.

## Blocking requests

An application can become unresponsive when it has to wait for an operation to finish before it can handle other work.

On the JVM, code runs on threads.
If the thread responsible for handling events has to wait for an operation to finish, it can't do other work in the meantime.
An operation that causes the thread to wait in this way is known as a _blocking operation_.

The `BlogServiceBlocking` class uses the Retrofit library to perform HTTP requests.
For example, its `getArticleInfoList()` function contains the following code:

```kotlin
fun getArticleInfoList(): List<ArticleInfo> {
    log("Started loading articles (blocking)")
    return retrofitService.getArticlesCall()
        .execute()
        .body()
        .orEmpty()
        .also {
            log("Loaded articles (blocking)")
        }
}
```

The `getArticlesCall()` function prepares an HTTP request.
The `execute()` function sends the request and blocks the current thread until the server returns a response.

### Task – Implement the blocking function

In the `Task1BlockVsSuspend.kt` file, replace the `TODO()` placeholder in the following function:

```kotlin
fun loadArticles(serviceBlocking: BlogServiceBlocking): List<Article> {
    TODO()
}
```

> Before implementing the function, open `desktop-client/src/jvmMain/kotlin/org/example/articles/network/BlogServiceBlocking.kt` and inspect the functions available for loading articles and comments.
> 
{style="tip"}

Then replace the `TODO()` placeholder with code that:

* Loads the available `ArticleInfo` objects.
* Loads the comments for each article.
* Combines each `ArticleInfo` object with its comments.
* Returns the resulting `Article` objects.

#### Solution for the blocking function {initial-collapse-state="collapsed" collapsible="true" id="blocking-function-solution"}

1. Call the `getArticleInfoList()` function and store the returned list.
2. Use the [`.map()`](https://kotlinlang.org/api/core/kotlin-stdlib/kotlin.collections/map.html) extension function to process each `ArticleInfo` object:
    * Call the `getComments()` function to load its comments.
    * Combine the `ArticleInfo` object and its comments into an `Article` object.
3. Return the list produced by `.map()`.

```kotlin
fun loadArticles(serviceBlocking: BlogServiceBlocking): List<Article> {
    val articleInfoList = serviceBlocking.getArticleInfoList()
    return articleInfoList.map { articleInfo: ArticleInfo ->
        Article(
            articleInfo,
            serviceBlocking.getComments(articleInfo)
        )
    }
}
```

### Observe the blocking behavior

[Run the application](coroutines-and-flows-tutorial.md#run-the-application), select **BLOCKING** from the **Loading Mode** menu, and click **Load comments**.

The application invokes the blocking `loadArticles()` function on the UI thread.
Each time `BlogServiceBlocking` invokes Retrofit's `execute()` function, the UI thread waits until the local server returns an HTTP response.
While it waits, the thread can't update the window or handle input.
As a result, the rotating emoji stops and the application remains unresponsive until all articles and comments have loaded.

![Result of running the blocking function](blocking-function.png){width="700"}

## Suspending functions

Kotlin provides [_suspending functions_](coroutines-basics.md#suspending-functions), which can pause at a _suspension point_ without blocking the thread and continue later from that point.
You can only call a suspending function from another suspending function.

To declare a suspending function, use the `suspend` keyword:

```kotlin
suspend fun suspendableComputation() { /* ... */ }
```

The `BlogService` interface declares `getArticleInfoList()` and `getComments()` as suspending functions.
The private `BlogServiceImpl` class implements these functions with Ktor, such as in the `getArticleInfoList()` function:

```kotlin
override suspend fun getArticleInfoList(): List<ArticleInfo> {
    log("Started loading articles")
    return client.get(articlesEndpoint)
        .body<List<ArticleInfo>>()
        .also {
            log("Loaded articles")
        }
}
```

Ktor's suspending [`.get()`](https://api.ktor.io/ktor-client-core/io.ktor.client.request/get.html) extension function sends the HTTP request.
While waiting for a response, the `getArticleInfoList()` function can suspend its execution without blocking the thread.
When the server returns a response, the function continues.

The `suspend` keyword doesn't make blocking code non-blocking by itself.
It declares a function as suspending, which allows the function to call other suspending functions.
Because `getArticleInfoList()` and `getComments()` are suspending functions, the second `loadArticles()` function also uses the `suspend` keyword.

### Coroutines

A [_coroutine_](coroutines-overview.md) is a suspendable computation that can pause and resume execution.
On the JVM, coroutines run on threads and can be suspended.
When a coroutine is suspended, the corresponding computation is paused, removed from the thread, and stored in memory.
Meanwhile, the thread is free to run other tasks:

![Suspending coroutines](suspension-process.gif){width=700}

New coroutines are launched in a [`CoroutineScope`](coroutines-basics.md#coroutine-scope-and-structured-concurrency).
A `CoroutineScope` defines the context in which its coroutines run and manages their lifecycle.

To start a coroutine, use a [_coroutine builder function_](coroutines-basics.md#coroutine-builder-functions) such as
[`.launch()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/launch.html).
The `.launch()` builder function accepts a suspending lambda that contains the code for the new coroutine.
Inside this lambda, you can call suspending functions.

In this project, `loadingScope` is the `CoroutineScope` used for loading articles.
Each time you click **Load comments** the `ArticlesViewModel.loadComments()` function in the
`desktop-client/src/jvmMain/kotlin/org/example/articles/ui/ArticlesViewModel.kt` file calls the
`.launch()` coroutine builder function and runs the selected loading mode inside it:

```kotlin
loadingJob = loadingScope.launch(coroutineExceptionHandler) {
    when (loadingMode) {
        BLOCKING -> {
            val articleList = loadArticles(blockingService)
            // ...
        }

        SUSPENDING -> {
            val articleList = loadArticles(service)
            // ...
        }

        // ...
    }
}
```

Because the block passed to `.launch()` is suspending, it can call the suspending `loadArticles(service)` function.

### Task — Implement the suspending function

In the `Task1BlockVsSuspend.kt` file, replace the `TODO()` placeholder in the following function:

```kotlin
suspend fun loadArticles(service: BlogService): List<Article> {
    TODO()
}
```

> Before implementing the function, open the `desktop-client/src/jvmMain/kotlin/org/example/articles/network/BlogService.kt` file and inspect the suspending functions available for loading articles and comments.
> 
{style="tip"}

Using the same loading process as in the [blocking implementation](#implement-the-blocking-function), replace the `TODO()` placeholder with code that:

* Loads the available `ArticleInfo` objects.
* Loads the comments for each article.
* Combines each `ArticleInfo` object with its comments.
* Returns the resulting `Article` objects.

#### Solution for the suspending function {initial-collapse-state="collapsed" collapsible="true" id="suspending-function-solution"}

1. Call the suspending `getArticleInfoList()` function and store the returned list.
2. Use the `.map()` extension function to process each `ArticleInfo` object:
   * Call the suspending `getComments()` function to load its comments.
   * Combine the `ArticleInfo` object and its comments into an `Article` object.
3. Return the list produced by `.map()`.

```kotlin
suspend fun loadArticles(service: BlogService): List<Article> {
    val articleInfoList = service.getArticleInfoList()
    return articleInfoList.map { articleInfo: ArticleInfo ->
        Article(
            articleInfo,
            service.getComments(articleInfo)
        )
    }
}
```

### Observe the suspending behavior

Run the application, select **SUSPENDING** from the **Loading Mode** menu, and click **Load comments**.

The application invokes the suspending `loadArticles()` function in a coroutine on the UI thread.
While the coroutine waits for an HTTP response, it suspends and allows the UI thread to handle other work.
As a result, the rotating emoji continues moving and the application remains responsive while the articles and comments load.

Loading still takes approximately 10 seconds because the application requests comments for one article at a time.
The coroutine can suspend while waiting for each response without blocking the UI thread, but the requests still run sequentially.

![Observing the suspending load mode](suspending-loading.png){width="700"}

In the next part of the tutorial, you'll send the comment requests concurrently to reduce the total loading time.

## Test your implementation

Run the tests in the `desktop-client/src/jvmTest/kotlin/org/example/articles/tasks/Task1BlockVsSuspendKtTest.kt` file.

The tests check that the suspending `loadArticles()` function returns the expected `Article` objects and loads their comments sequentially.
They use virtual time, so you don't have to wait for the simulated delays.

## Next step

<list columns="2" id="tour-nav">
  <li>
    <a as="button" href="coroutines-and-flows-tutorial.md" mode="outline" icon="arrow-left" icon-position="left">Previous step</a>
  </li>
  <li>
    <a as="button" href="coroutines-tutorial-concurrent-loading.md" mode="classic" icon="arrow-right" icon-position="right">Next step</a>
  </li>
</list>