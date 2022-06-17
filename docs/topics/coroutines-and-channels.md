[//]: # (title: Coroutines and channels − tutorial)

In this tutorial, you'll see how to use coroutines to perform network requests without blocking the underlying thread or
callbacks.

You'll learn:

* Why and how to use suspend functions to perform network requests
* How to send requests concurrently using coroutines
* How to share information between different coroutines using channels

For network requests, you'll need the [Retrofit](https://square.github.io/retrofit/) library, which already
supports coroutines, but the approach shown in this tutorial is universal and works similarly for different libraries.

This tutorial is based on the [Asynchronous Programming with Kotlin](https://kotlinconf.com/workshops/) workshop by
Roman Elizarov at KotlinConf.

> You're expected to be familiar with basic Kotlin syntax, but prior knowledge of coroutines is not required.
>
{type="tip"}

You can find solutions for all the tasks on the `solutions` branch to compare with your solution.

## Before you start

Download and install the latest version of [IntelliJ IDEA](https://www.jetbrains.com/idea/download/index.html).
Clone the [project template](http://github.com/kotlin-hands-on/intro-coroutines) by choosing **Get from VCS** on the
welcome screen or selecting **File | New | Project from Version Control**. You can also clone it from the command line:

```
git clone https://github.com/kotlin-hands-on/intro-coroutines
```

### Generate GitHub developer token

You'll be using GitHub API in your project. To get access, specify your GitHub account name and either a password or a
token. If you have two-factor authentication enabled, a token will be enough.

Generate a new GitHub token to use GitHub API [from your account](https://github.com/settings/tokens/new).
Specify the name of your token, for example, `coroutines-hands-on`:

![Generate a new GitHub token](generating-token.png)

There is no need to select any scopes, click on **Generated token** at the bottom.
Copy the generated token.

### Run the code

The program loads the contributors for all the repositories under the given organization. By default, the organization
is "kotlin," but it could be any other. Later you'll add logic to sort the users by the number of their contributions.

1. Open the `src/contributors/main.kt` file and run the `main()` function. You'll see a window like that (but without any
   data loaded):

   ![First window](initial-window.png)

   If the fonts are too small, adjust them by specifying a different default size in the `main()` function.

2. Fill in the GitHub username and token (or password) in the corresponding fields.
3. Make sure that the 'BLOCKING' option
   is chosen in the variant dropdown menu and click **Load contributors**.

The UI should freeze for some time and then show the list of the contributors.

* You can open the program output to ensure the data is loaded.
* The information is logged after each successful request.
* Make sure the loaded data can be seen before continuing.

There are different ways of implementing this logic: a [blocking request](#blocking request)
and [using-callbacks](#callbacks). You'll compare these solutions with one that uses coroutines and see how to use
channels to share information between different coroutines.

## Blocking request

You will use the [Retrofit](https://square.github.io/retrofit/) library to perform HTTP requests to GitHub. It allows
requesting the list of repositories under the given organization and the list of contributors for each repository:

```kotlin
interface GitHubService {
    @GET("orgs/{org}/repos?per_page=100")
    fun getOrgReposCall(
        @Path("org") org: String
    ): Call<List<Repo>>

    @GET("repos/{owner}/{repo}/contributors?per_page=100")
    fun getRepoContributorsCall(
        @Path("owner") owner: String,
        @Path("repo") repo: String
    ): Call<List<User>>
}
```

1. Open `src/tasks/Request1Blocking.kt` and check the implementation of the function `loadContributorsBlocking()`. It
   fetches the list of contributors for the given organization.

    ```kotlin
    fun loadContributorsBlocking(service: GitHubService, req: RequestData): List<User> {
        val repos = service
            .getOrgReposCall(req.org)   // #1
            .execute()                  // #2
            .also { logRepos(req, it) } // #3
            .body() ?: emptyList()      // #4
    
        return repos.flatMap { repo ->
            service
                .getRepoContributorsCall(req.org, repo.name) // #1
                .execute()                                   // #2
                .also { logUsers(repo, it) }                 // #3
                .bodyList()                                  // #4
        }.aggregate()
    }
    ```

    * At first, you get a list of the repositories under the given organization and store it in the `repos` list. Then for
      each repository, the list of contributors is requested, and all the lists get merged into one final list of
      contributors.
    * Each `getOrgReposCall()` and `getRepoContributorsCall()` returns an instance of the `Call` class(`#1`). At this point,
      no request is sent.
    * `Call.execute` is then invoked to perform the request (`#2`). `execute` is a synchronous call that blocks the
      underlying thread.
    * When you get the response, the result is logged by calling the specific `logRepos()` and `logUsers()` functions (`#3`)
      . If the HTTP response contains an error, this error will be logged here.
    * Lastly, get the response's body, which contains the desired data. For this tutorial, you'll use an empty list as a
      result in case
      there is an error and log the corresponding error (`#4`).

2. To avoid repeating `.body() ?: emptyList()` over and over, declare an extension
   function `bodyList()`:

    ```kotlin
    fun <T> Response<List<T>>.bodyList(): List<T> {
        return body() ?: emptyList()
    }
    ```  

3. `logRepos` and `logUsers` log the received information straight away.

While running the code, look at the system output. It should show something like this:

```
1770 [AWT-EventQueue-0] INFO  Contributors - kotlin: loaded 40 repos
2025 [AWT-EventQueue-0] INFO  Contributors - kotlin-examples: loaded 23 contributors
2229 [AWT-EventQueue-0] INFO  Contributors - kotlin-koans: loaded 45 contributors
...
```

* The first item on each line is the amount of milliseconds that have passed since the program started, then the thread
  name in square brackets. You can see from which thread the loading request is called on.
* The final item on each line is the actual message: how many repositories or contributors were loaded.

This log demonstrates that all the results were logged from the main thread. When you run the code under a `BLOCKING`
request, the window freezes and don't react to input until the loading is finished. All the requests are executed from
the same thread as the one called `loadContributorsBlocking` from, which is the main UI thread (in Swing it's an AWT
event dispatching thread). This main thread gets blocked, and that's why the UI is frozen:

![The blocked main thread](blocking.png)

After the list of contributors has loaded, the result is updated. If you look at how `loadContributorsBlocking` is
called, you'll find that the `updateResults` goes right after the `loadContributorsBlocking` call:

```kotlin
val users = loadContributorsBlocking(service, req)
updateResults(users, startTime)
```

You can find this code in `src/contributors/Contributors.kt`.

* The `loadContributors()` function is responsible for choosing how the contributors are loaded.
* The `updateResults()` function updates the UI. As a result, it must always be called from the UI thread.

#### Task

To familiarize yourself with the task domain, complete the following task.

Currently, each contributor's name is repeated several times, once for every project they have taken part in. The task
is to implement the `aggregate` function combining the users so that each contributor is added only once.
The `User.contributions` property should contain the total number of contributions of the given user to _all_ of the
projects. The resulting list should be sorted in descending order according to the number of contributions.

Open `src/tasks/Aggregation.kt` and implement `List<User>.aggregate()` function. The corresponding test
file `test/tasks/AggregationKtTest.kt` shows an example of the expected result.

You can jump between the source code and the test class automatically [using the IntelliJ IDEA
shortcut](https://www.jetbrains.com/help/idea/create-tests.html#test-code-navigation).

After implementing this task, the resulting list for the "Kotlin" organization should be similar to the following:

![The list for the "Kotlin" organization](aggregate.png)

> Users are sorted by the total number of their contributions.
>
{type="note"}

#### Solution {initial-collapse-state="collapsed"}

Group users by their login. You can use
[`groupBy()`](https://kotlinlang.org/api/latest/jvm/stdlib/kotlin.collections/group-by.html) that returns a map from
login to all occurrences of the user with this login in different repositories.
For each map entry, count the total number of contributions for each user and create a new instance of the `User` class
by the given name and sum of contributions.
Sort the resulting list in descending order.

```kotlin
fun List<User>.aggregate(): List<User> =
    groupBy { it.login }
        .map { (login, group) -> User(login, group.sumOf { it.contributions }) }
        .sortedByDescending { it.contributions }
```

An alternative is to use
the [`groupingBy`](https://kotlinlang.org/api/latest/jvm/stdlib/kotlin.collections/grouping-by.html)function instead
of `groupBy`.

## Using callbacks

The previous solution works, but blocks the thread and therefore freezes the UI. A traditional approach to avoiding this
is to use callbacks.

Instead of calling the code that should be invoked after the operation is completed straightaway, you can extract it
into a separate callback, often a lambda, and pass this lambda to the caller in order for it to be called later.

To make the UI responsive, you can either move the whole computation to a separate thread or switch to Retrofit API and
start using callbacks instead of blocking calls.

### Calling `loadContributorsBlocking()` in the background thread

First, move the whole computation to a different thread. For that, use the `thread()` function to start a new thread:

```kotlin
thread {
    loadContributorsBlocking(service, req)
}
```

Now that all the loading has been moved to a separate thread, the main thread is free and can be occupied with different
tasks:

![The freed main thread](background.png)

The signature of the `loadContributorsBackground()` function changes. It takes a `updateResults`
callback as the last argument to call it after all the loading completes:

```kotlin
fun loadContributorsBackground(
    service: GitHubService, req: RequestData,
    updateResults: (List<User>) -> Unit
)
```

Now when the `loadContributorsBackground()` is called, the `updateResults` call goes in the callback, not immediately
afterward as it did before:

```kotlin
loadContributorsBackground(service, req) { users ->
    SwingUtilities.invokeLater {
        updateResults(users, startTime)
    }
}
```

By calling `SwingUtilities.invokeLater`, you ensure that the `updateResults` call, which updates the results, happens on
the main UI thread(AWT event dispatching thread).

However, if you try to load the contributors via the `BACKGROUND` option, you can see that the list is updated, but
nothing changes.

#### Task

Fix the `loadContributorsBackground()` in `src/tasks/Request2Background.kt` so that the resulting list was shown in the
UI.

#### Solution {initial-collapse-state="collapsed"}

Now the contributors are loaded, as you can see in the log, but the result isn't displayed. To fix this, call
the `updateResults` on the resulting list of users:

```kotlin
thread {
    updateResults(loadContributorsBlocking(service, req))
}
```

You should make sure to call the logic passed in the callback explicitly. Otherwise, nothing will happen.

### Using Retrofit callback API

In the previous solution, the whole loading logic is moved to the background thread, but it's still not the best use of
resources. All the loading requests go sequentially one after another, and while waiting for the loading result, the
thread is blocked, but it could be occupied with some other tasks. Specifically, it could start another loading to
receive the whole result earlier.

Handling the data for each repository should be then divided into two parts: first, the loading, then processing the
resulting response.
The second _processing_ part should be extracted into a callback.

The loading for each repository can then be started before the result for the previous repository is received (and the
corresponding callback is called):

![Using callback API](callbacks.png)

The Retrofit callback API can help achieve that. The `Call.enqueue()` function starts an HTTP request and takes a
callback as an argument. In this callback, you need to specify what needs to be done after each request.

`loadContributorsCallbacks()` in `src/tasks/Request3Callbacks.kt` uses this API. For convenience, the `onResponse()`
extension function declared in the same file is used. It takes a lambda as an argument rather than an object expression:

```kotlin
fun loadContributorsCallbacks(
    service: GitHubService, req: RequestData,
    updateResults: (List<User>) -> Unit
) {
    service.getOrgReposCall(req.org).onResponse { responseRepos ->  // #1
        logRepos(req, responseRepos)
        val repos = responseRepos.bodyList()

        val allUsers = mutableListOf<User>()
        for (repo in repos) {
            service.getRepoContributorsCall(req.org, repo.name).onResponse { responseUsers ->   // #2
                logUsers(repo, responseUsers)
                val users = responseUsers.bodyList()
                allUsers += users
            }
        }
        // TODO: Why this code doesn't work? How to fix that?
        updateResults(allUsers.aggregate())
    }
}
```

The logic handling the responses is extracted into callbacks: the corresponding lambdas start at lines `#1` and `#2`.

However, the provided solution doesn't work. If you run the program and load contributors by choosing the `CALLBACKS`
option, you can see that nothing is shown. The tests that immediately return the result, however, pass.

Think about why the given code doesn't work as expected and try to fix it or check the solution below.

#### Task (optional)

Rewrite the code so that the loaded list of contributors is shown.

#### Solution (first attempt)  {initial-collapse-state="collapsed"}

Now many requests are started concurrently, which decreases the total loading time. However, the result isn't loaded.
The `updateResults` callback is called right after all the loading requests are started, so the `allUsers` list is not
yet filled with the data.

You can try to fix this with the following change:

```kotlin
val allUsers = mutableListOf<User>()
for ((index, repo) in repos.withIndex()) {   // #1
    service.getRepoContributorsCall(req.org, repo.name).onResponse { responseUsers ->
        logUsers(repo, responseUsers)
        val users = responseUsers.bodyList()
        allUsers += users
        if (index == repos.lastIndex) {      // #2
            updateResults(allUsers.aggregate())
        }
    }
} 
```

* First, you iterate over the list of repos with an index (`#1`).
* Then, from each callback, you check whether it's the last iteration (`#2`).
* And if that's the case, the result is updated.

However, this code is also incorrect. Try to find an answer yourself or check the solution below.

#### Solution (second attempt) {initial-collapse-state="collapsed"}

Since the loading requests are started concurrently, no one guarantees that the result for the last one comes last. The
results can come in any order.

So, if you compare the current index with the `lastIndex` as a condition for completion, you risk losing the results for
some of the repos.

If the request processing the last repo returns faster than some prior requests (which is likely to happen), all the
results for requests that take more time will be lost.

One of the ways to fix this is to introduce an index and check whether all the repositories are already processed:

```kotlin
val allUsers = Collections.synchronizedList(mutableListOf<User>())
val numberOfProcessed = AtomicInteger()
for (repo in repos) {
    service.getRepoContributorsCall(req.org, repo.name).onResponse { responseUsers ->
        logUsers(repo, responseUsers)
        val users = responseUsers.bodyList()
        allUsers += users
        if (numberOfProcessed.incrementAndGet() == repos.size) {
            updateResults(allUsers.aggregate())
        }
    }
}
```

> An asynchronized version of the list and `AtomicInteger` are used because, in general, there's no guarantee that
> different callback processing `getRepoContributors` requests will always be called from the same thread.
>
type={"note"}

#### Solution (third attempt) {initial-collapse-state="collapsed"}

An even better solution is to use the `CountDownLatch` class. It stores a counter initialized with the number of
repositories. This counter is decremented after processing each repository. It then waits until the latch is counted
down to zero before updating the results:

```kotlin
val countDownLatch = CountDownLatch(repos.size)
for (repo in repos) {
    service.getRepoContributorsCall(req.org, repo.name).onResponse { responseUsers ->
        // processing repository
        countDownLatch.countDown()
    }
}
countDownLatch.await()
updateResults(allUsers.aggregate())
```

The result is then updated from the main thread, which is more direct than delegating this logic to the child threads.

You can see that writing the correct code with callbacks might be non-trivial and error-prone, especially when several
underlying threads and synchronization occur.

> As an additional exercise, you can implement the same logic using a reactive approach with the RxJava library. All the
> necessary dependencies and solutions for using RxJava can be found in a separate `rx` branch. It is also possible to
> complete this tutorial and implement or check the proposed Rx versions for a proper comparison.
>
{type="tip"}

## Using suspending functions

You can implement the same logic using suspending functions. Instead of returning `Call<List<Repo>>`, define the API
call as a [suspending function](composing-suspending-functions.md):

```kotlin
interface GitHubService {
    @GET("orgs/{org}/repos?per_page=100")
    suspend fun getOrgRepos(
        @Path("org") org: String
    ): List<Repo>
}
```

* When you use a suspending function to perform a request, the underlying thread isn't blocked.
* `getOrgRepos()` returns the result directly instead of returning a `Call`.
* If the result is unsuccessful, an exception is thrown.

Alternatively, Retrofit also allows returning the result wrapped in `Response`. In this case, the result body is
provided, and it is possible to check for errors manually.

Add the following declarations to `GitHubService`:

```kotlin
interface GitHubService {
    // getOrgReposCall & getRepoContributorsCall declarations

    @GET("orgs/{org}/repos?per_page=100")
    suspend fun getOrgRepos(
        @Path("org") org: String
    ): Response<List<Repo>>

    @GET("repos/{owner}/{repo}/contributors?per_page=100")
    suspend fun getRepoContributors(
        @Path("owner") owner: String,
        @Path("repo") repo: String
    ): Response<List<User>>
}
```

#### Task

The task is to change the code of the function loading contributors to make use of the new suspending functions.

A suspending function can't be called everywhere. There will be an error if it's called
from `loadContributorsBlocking()`.

Mark the new version of the `loadContributors()` function as `suspend` to use this new API.
Copy the implementation of `loadContributorsBlocking()` defined in `src/tasks/Request1Blocking.kt`
into `loadContributorsSuspend()` defined in `src/tasks/Request4Suspend.kt`.
Modify so that the new suspending functions are used instead of ones returning `Call`s.
Run the program by choosing the `SUSPEND` option and ensure that the UI is still responsive while the GitHub requests
are performed.

#### Solution {initial-collapse-state="collapsed"}

Replace `.getOrgReposCall(req.org).execute()` with `.getOrgRepos(req.org)` and repeat the same replacement for the
second "contributors" request:

```kotlin
suspend fun loadContributorsSuspend(service: GitHubService, req: RequestData): List<User> {
    val repos = service
        .getOrgRepos(req.org)
        .also { logRepos(req, it) }
        .bodyList()

    return repos.flatMap { repo ->
        service.getRepoContributors(req.org, repo.name)
            .also { logUsers(repo, it) }
            .bodyList()
    }.aggregate()
}
```

> `loadContributorsSuspend()` should be defined as a `suspend` function.
>
{type="note"}

You no longer need to call `execute`, which returned the `Response` before, because now the API functions return
the `Response` directly.
But that's an implementation detail specific to the Retrofit library.
With other libraries, the API will be different, but the concept is the same.

## Coroutines

The code with suspending functions looks similar to the "blocking" version. The major difference with a blocking version
is that instead of blocking the thread, the coroutine is suspended:

```
block -> suspend
thread -> coroutine
```

Coroutines are often called lightweight threads because you can run code on coroutines, similar to how you run code on
threads. The operations that were blocking before (and had to be avoided)can now suspend the coroutine instead.

### Starting a new coroutine

If you look at how `loadContributorsSuspend()` is called, you can see that it's called inside `launch`. `launch` is a
library function that takes a lambda as an argument:

```kotlin
launch {
    val users = loadContributorsSuspend(req)
    updateResults(users, startTime)
}
```

`launch` starts a new computation. This computation is responsible for loading the data and showing the results. This
computation is suspendable: it gets suspended
and releases the underlying thread while performing the network requests. When the network request returns the result,
the computation is resumed.

Such a suspendable computation is called a coroutine. So, in this case, `launch` _starts a new coroutine_ responsible
for loading data and showing the results.

Coroutines are computations that run on top of threads and can be suspended. When a coroutine is suspended, the
corresponding computation is paused, removed from the thread, and stored in memory. Meanwhile, the thread is free to be
occupied with other activities:

![Suspending coroutines](suspension-process.gif)

When the computation is ready to be continued, it gets returned to a thread (but not necessarily to the same one).

In the `loadContributorsSuspend()` example, each "contributors" request now waits for the result using the suspension
mechanism. First, the new request is sent. Then, while waiting for the response, the whole "load contributors" coroutine
becomes suspended (the one started by the `launch` function).

The coroutine resumes only after the corresponding response is received:

![Suspending request](suspend-requests.png)

While the response is waiting to be received, the thread is free to be occupied with other tasks. That's why when users
are loaded using the `SUSPEND` option, the UI stays responsive, despite all the requests taking place on the
main UI thread.

The log confirms that all the requests are sent on the main UI thread:

```
2538 [AWT-EventQueue-0 @coroutine#1] INFO  Contributors - kotlin: loaded 30 repos
2729 [AWT-EventQueue-0 @coroutine#1] INFO  Contributors - ts2kt: loaded 11 contributors
3029 [AWT-EventQueue-0 @coroutine#1] INFO  Contributors - kotlin-koans: loaded 45 contributors
...
11252 [AWT-EventQueue-0 @coroutine#1] INFO  Contributors - kotlin-coroutines-workshop: loaded 1 contributors
```

The log can also show you what coroutine the corresponding code runs on. To enable it, open **Run | Edit
configurations** and add the `-Dkotlinx.coroutines.debug` VM option:

![Edit run configuration](run-configuration.png)

Then while running `main()` with this option, the coroutine name will be attached to the thread name. You can also
modify the template for running all the Kotlin files and enable this option by default.

In this case, all the code runs on one coroutine, the mentioned above "load contributors" coroutine, denoted
as `@coroutine#1`.

In this version, while waiting for the result, you don't reuse the thread for sending other requests because the code is
written sequentially. The new request is sent only when the previous result is received.

Suspending functions treat the thread fairly and don't block it for "waiting", but it doesn't yet bring any concurrency
to the picture.

## Concurrency

Kotlin coroutines are extremely inexpensive in comparison to threads.
Each time you want to start a new computation asynchronously, you can create a new coroutine.

To start a new coroutine, one of the main _coroutine builders_ is used: `launch`, `async`, or `runBlocking`. Different
libraries can define additional coroutine builders.

* `async` starts a new coroutine and returns a `Deferred` object.
  `Deferred` represents a concept known by other names such as `Future` or `Promise`:
* It stores a computation, but it _defers_ the moment you get the final result;
* It _promises_ the result sometime in the _future_.

The main difference between `async` and `launch` is that `launch` is used to start a computation that isn't expected to
return a specific result. `launch` returns `Job`, representing the coroutine. It is possible to wait until it completes
by calling `Job.join()`.

`Deferred` is a generic type that extends `Job`. An `async` call can return a `Deferred<Int>` or `Deferred<CustomType>`
depending on what the lambda returns (the last expression inside the lambda is the result).

To get the result of a coroutine, call `await()` on the `Deferred` instance. While waiting for the result, the coroutine
that this `await` is called from suspends:

```kotlin
import kotlinx.coroutines.*

fun main() = runBlocking {
    val deferred: Deferred<Int> = async {
        loadData()
    }
    println("waiting...")
    println(deferred.await())
}

suspend fun loadData(): Int {
    println("loading...")
    delay(1000L)
    println("loaded!")
    return 42
}
```

* `runBlocking` is used as a bridge between regular and suspending functions, blocking and non-blocking worlds. It works
  as an adaptor for starting the top-level main coroutine. It is intended primarily to be used in `main()` functions and
  tests.

To get a better understanding, watch the following video:

![Video explaining the coroutines sample](zEZc5AmHQhk)

If there is a list of deferred objects, it is possible to call `awaitAll()` to await the results of all of them:

```kotlin
import kotlinx.coroutines.*

fun main() = runBlocking {
    val deferreds: List<Deferred<Int>> = (1..3).map {
        async {
            delay(1000L * it)
            println("Loading $it")
            it
        }
    }
    val sum = deferreds.awaitAll().sum()
    println("$sum")
}
```

When starting each "contributors" request in a new coroutine, all the requests are started asynchronously. A new request
can be sent before the result for the previous one is received:

![Concurrent coroutines](concurrency.png)

The total loading time is approximately the same as in the `CALLBACKS` version, but it doesn't need any callbacks.
What's more, `async` explicitly emphasizes which parts run concurrently in the code.

#### Task

In the `Request5Concurrent.kt` file, implement a `loadContributorsConcurrent()` function. For that, use the
previous `loadContributorsSuspend()` function.

#### Tip {initial-collapse-state="collapsed"}

As you'll see later, you can only start a new coroutine inside a coroutine scope. Copy the content
from `loadContributorsSuspend()` to the `coroutineScope` call, so that you can call `async` functions there:

```kotlin
suspend fun loadContributorsConcurrent(
    service: GitHubService, req: RequestData
): List<User> = coroutineScope {
    // ...
}
```

Base the solution on the following scheme:

```kotlin
val deferreds: List<Deferred<List<User>>> = repos.map { repo ->
    async {
        // load contributors for each repo
    }
}
deferreds.awaitAll() // List<List<User>>
```

#### Solution {initial-collapse-state="collapsed"}

Wrap each "contributors" request with `async` to create as many coroutines as the number of repositories. `async`
returns `Deferred<List<User>>`.

Since it's really inexpensive to create a new coroutine, it's not an issue. You can create as many as you need.

You can no longer use `flatMap` because the `map` result is now a list of `Deferred` objects, not a list of lists.
`awaitAll()` returns `List<List<User>>`, so to get the result, call `flatten().aggregate()`:

```kotlin
suspend fun loadContributorsConcurrent(service: GitHubService, req: RequestData): List<User> = coroutineScope {
    val repos = service
        .getOrgRepos(req.org)
        .also { logRepos(req, it) }
        .bodyList()

    val deferreds: List<Deferred<List<User>>> = repos.map { repo ->
        async {
            service.getRepoContributors(req.org, repo.name)
                .also { logUsers(repo, it) }
                .bodyList()
        }
    }
    deferreds.awaitAll().flatten().aggregate()
}
```

Run the code and check the log. You can see that all the coroutines still run on the main UI thread because
multithreading isn't employed yet. But there are already benefits of running coroutines concurrently.

To change this code to run "contributors" coroutines on different threads from the common thread pool,
specify `Dispatchers.Default` as the context argument for the `async` function:

```kotlin
async(Dispatchers.Default) { }
```

`CoroutineDispatcher` determines what thread or threads the corresponding coroutine should be run on. If you don't
specify one as an argument, `async` will use the dispatcher from the outer scope.

`Dispatchers.Default` represents a shared pool of threads on JVM.
This pool provides a means for parallel execution.
It consists of as many threads as CPU cores available, but it still has two threads if there's only one core.

Modify the code in the `loadContributorsConcurrent()` function to start new coroutines on different threads from the
common thread pool.
Also, add additional logging before sending the request:

```kotlin
async(Dispatchers.Default) {
    log("starting loading for ${repo.name}")
    service.getRepoContributors(req.org, repo.name)
        .also { logUsers(repo, it) }
        .bodyList()
}
```

After introducing this change, you can observe in the log that each coroutine can be started on one thread from the
thread pool and resumed on another:

```
1946 [DefaultDispatcher-worker-2 @coroutine#4] INFO  Contributors - starting loading for kotlin-koans
1946 [DefaultDispatcher-worker-3 @coroutine#5] INFO  Contributors - starting loading for dokka
1946 [DefaultDispatcher-worker-1 @coroutine#3] INFO  Contributors - starting loading for ts2kt
...
2178 [DefaultDispatcher-worker-1 @coroutine#4] INFO  Contributors - kotlin-koans: loaded 45 contributors
2569 [DefaultDispatcher-worker-1 @coroutine#5] INFO  Contributors - dokka: loaded 36 contributors
2821 [DefaultDispatcher-worker-2 @coroutine#3] INFO  Contributors - ts2kt: loaded 11 contributors
```

For instance, in this log excerpt, `coroutine#4` is started on the thread `worker-2` and continued on the
thread `worker-1`.

To run the coroutine only on the main UI thread, specify `Dispatchers.Main` as an argument:

```kotlin
launch(Dispatchers.Main) {
    updateResults()
}
```

If the main thread is busy when you start a new coroutine on it,
the coroutine becomes suspended and scheduled for execution on this thread. The coroutine will only resume when the
thread becomes free.

It's considered good practice to use the dispatcher from the outer scope rather than explicitly specify it on each
end-point. In the case when `loadContributorsConcurrent()` is defined without passing `Dispatchers.Default` as an
argument, you can then call this function in any way: in the context with a `Default` dispatcher, in the context with
the main UI thread, or the context with a custom dispatcher.

As you'll see later, when calling `loadContributorsConcurrent()` from tests, you can call it in the context
with `TestCoroutineDispatcher` which simplifies testing. Thus, this solution is much more flexible.

To specify the dispatcher on the caller-side, apply the following change to the project while
letting `loadContributorsConcurrent` start coroutines in the inherited context:

```kotlin
launch(Dispatchers.Default) {
    val users = loadContributorsConcurrent(service, req)
    withContext(Dispatchers.Main) {
        updateResults(users, startTime)
    }
}
```

* `updateResults()` should be called on the main UI thread, so you call it with the context of `Dispatchers.Main`.
* `withContext()` calls the given code with the specified coroutine context, suspends until it completes, and returns
  the result.

Run the code and ensure that the coroutines are executed on the threads from the thread pool.

An alternative but a more verbose way to express this would be to start a new coroutine and explicitly wait (by
suspending) until it completes: `launch(context) { ... }.join()`.

## Structured concurrency

* _Coroutine scope_ is responsible for the structure and parent-child relationships between different coroutines.
Coroutine builders, like `launch` and `async`, need to be started in some scope.
* _Coroutine context_ stores additional technical information used to run a given coroutine, like the coroutine custom
name, or the dispatcher specifying the threads the coroutine should be scheduled on.

When `launch`, `async`, or `runBlocking` are used to start a new coroutine, they automatically create the corresponding
scope. All these functions take a lambda with a receiver as an argument, and the implicit receiver type is
the `CoroutineScope`:

```kotlin
launch { /* this: CoroutineScope */
}
```

New coroutines can only be started inside a scope. `launch` and `async` are declared as extensions to `CoroutineScope`,
so an implicit or explicit receiver must always be passed when you call them.

The coroutine started by `runBlocking` is the only exception because `runBlocking` is defined as a top-level function.
But because it blocks the current thread, it's intended primarily to be used in `main()` functions and tests as a bridge
function.

A new coroutine inside `runBlocking`, `launch`, or `async` is started automatically inside the scope:

```kotlin
import kotlinx.coroutines.*

fun main() = runBlocking { /* this: CoroutineScope */
    launch { /* ... */ }
    // the same as:   
    this.launch { /* ... */ }
}
```

When you call `launch` inside `runBlocking`, it's called as an extension to the implicit receiver of
the `CoroutineScope` type. Alternatively, you could explicitly write `this.launch`.

The nested coroutine (started by `launch` in this example) can be considered as a child of the outer coroutine (started
by `runBlocking`). This "parent-child" relationship works through scopes; the child coroutine is started from the scope
corresponding to the parent coroutine.

It's possible to create a new scope without starting a new coroutine.
The `coroutineScope` function does this.
To start new coroutines in a structured way inside a `suspend` function without access to the outer scope, for example
inside `loadContributorsConcurrent`, you can create a new coroutine scope which automatically becomes a child of the
outer scope that this `suspend` function is called from.

It's also possible to start a new coroutine from the global scope using `GlobalScope.async` or `GlobalScope.launch`.
This will create a top-level "independent" coroutine.

The mechanism providing the structure of the coroutines is called "structured concurrency".

See what benefits structured concurrency has over global scopes:

* The scope is generally responsible for child coroutines, and their lifetime is attached to the lifetime of the scope.
* The scope can automatically cancel child coroutines if something goes wrong or a user changes their mind and decides
  to revoke the operation.
* The scope automatically waits for the completion of all the child coroutines.
  Therefore, if the scope corresponds to a coroutine, the parent coroutine does not complete until all the coroutines
  launched in its scope are complete.

When using `GlobalScope.async` there is no structure that binds several coroutines to a smaller scope.
The coroutines started from the global scope are all independent;
their lifetime is limited only by the lifetime of the whole application.
It's possible to store a reference to the coroutine started from the global scope and wait for its completion or cancel
it explicitly, but it won't happen automatically as it would with a structured one.

### Cancellation of contributors loading

Consider two versions of the `loadContributorsConcurrent()` function.
The first uses `coroutineScope` to start all the child coroutines and the second uses `GlobalScope`. Compare how both
versions behave when trying to cancel the parent coroutine.

You can add a 3-second delay to all the coroutines sending requests, so that there's enough time to cancel the loading
after the coroutines are started, but before the requests are sent:

```kotlin
suspend fun loadContributorsConcurrent(service: GitHubService, req: RequestData): List<User> = coroutineScope {
    // ...
    async {
        log("starting loading for ${repo.name}")
        delay(3000)
        // load repo contributors
    }
    // ...
    result
}
```

In `Request5NotCancellable.kt`, copy the implementation of `loadContributorsConcurrent()`
to `loadContributorsNotCancellable()` () and remove the creation of a new `coroutineScope`.
The `async` calls now fail to resolve, so start them using `GlobalScope.async`:

```kotlin
suspend fun loadContributorsNotCancellable(service: GitHubService, req: RequestData): List<User> {   // #1
    // ...
    GlobalScope.async {   // #2
        log("starting loading for ${repo.name}")
        delay(3000)
        // load repo contributors
    }
    // ...
    return result  // #3
}
```

The function now returns the result directly, not as the last expression inside the lambda (lines `#1` and `#3`),
and all of the "contributors" coroutines are started inside the `GlobalScope`, not as children of the coroutine scope (
line `#2`).

Start by running the program and choosing to load the contributors using the `CONCURRENT` version, wait until all the "
contributors" coroutines are started, and then click on "cancel".
In the log, you can see that all the requests were indeed canceled because no results were logged:

```
2896 [AWT-EventQueue-0 @coroutine#1] INFO  Contributors - kotlin: loaded 40 repos
2901 [DefaultDispatcher-worker-2 @coroutine#4] INFO  Contributors - starting loading for kotlin-koans
...
2909 [DefaultDispatcher-worker-5 @coroutine#36] INFO  Contributors - starting loading for mpp-example
/* click on 'cancel' */
/* no requests are sent */
```

Repeat the same procedure but this time choose the `NOT_CANCELLABLE` option:

```
2570 [AWT-EventQueue-0 @coroutine#1] INFO  Contributors - kotlin: loaded 30 repos
2579 [DefaultDispatcher-worker-1 @coroutine#4] INFO  Contributors - starting loading for kotlin-koans
...
2586 [DefaultDispatcher-worker-6 @coroutine#36] INFO  Contributors - starting loading for mpp-example
/* click on 'cancel' */
/* but all the requests are still sent: */
6402 [DefaultDispatcher-worker-5 @coroutine#4] INFO  Contributors - kotlin-koans: loaded 45 contributors
...
9555 [DefaultDispatcher-worker-8 @coroutine#36] INFO  Contributors - mpp-example: loaded 8 contributors
```

In this case, no coroutines are canceled, and all the requests are still sent.

Now implement the cancellation in your "contributors" program. When the `cancel` button is clicked, explicitly cancel
the main "loading" coroutine. Then it automatically cancels all the child coroutines:

```kotlin
interface Contributors {

    fun loadContributors() {
        // ...
        when (getSelectedVariant()) {
            CONCURRENT -> {
                launch {
                    val users = loadContributorsConcurrent(req)
                    updateResults(users, startTime)
                }.setUpCancellation()      // #1
            }
        }
    }

    private fun Job.setUpCancellation() {
        val loadingJob = this              // #2

        // cancel the loading job if the 'cancel' button was clicked:
        val listener = ActionListener {
            loadingJob.cancel()            // #3
            updateLoadingStatus(CANCELED)
        }
        addCancelListener(listener)

        // update the status and remove the listener after the loading job is completed
    }
}   
```

The `launch` function returns an instance of `Job`.
`Job` stores a reference to the "loading coroutine", which loads all the data and updates the results.
You can call the `setUpCancellation()` extension function on it (line `#1`), passing an instance of `Job` as a receiver.
Another way you could express this would be to explicitly write:

```kotlin
val job = launch { }
job.setUpCancellation()
```

For readability, you could refer to the `setUpCancellation()` function receiver inside the function with the
new `loadingJob` variable (line `#2`). Then you can add a listener to the `cancel` button,
so then when it's clicked, the `loadingJob` is canceled (line `#3`).

With structured concurrency, you only need to cancel the parent coroutine and this automatically propagates cancellation
to all the child coroutines.

### Using the outer scope's context

When you start new coroutines inside the given scope, it's much easier to ensure that all of them are run with the same
context. And it's much easier to replace the context if needed.

Now it's time to learn how "using the dispatcher from the outer scope" works. The new scope created by
the `coroutineScope` or by the coroutine builders, always inherits the context from the outer scope. In this case, the
outer scope is the scope the `suspend loadContributorsConcurrent()` was called from:

```kotlin
launch(Dispatchers.Default) {  // outer scope
    val users = loadContributorsConcurrent(service, req)
    // ...
}
```

All the nested coroutines are automatically started with the inherited context. The dispatcher is a part of this
context. That's why all the coroutines started by `async` are started with the context of the default dispatcher:

```kotlin
suspend fun loadContributorsConcurrent(
    service: GitHubService, req: RequestData
): List<User> = coroutineScope {
    // this scope inherits the context from the outer scope
    // ...
    async {   // nested coroutine started with the inherited context
        // ...
    }
    // ...
}
```

With structured concurrency, you can specify the major context elements (like dispatcher) once, when creating a
top-level coroutine.
All the nested coroutines then inherit the context and modify it only if needed.

> When you write code with coroutines for UI applications, for example for Android, it is a common practice to
> use `CoroutineDispatchers.Main` by default for the top coroutine and then to explicitly put a different dispatcher when
> you need to run the code on a different thread.
>
{type="note"}

## Showing progress

Despite the information for some repositories being loaded rather fast, the user only sees the resulting list when all
the data is loaded. Until then, the loader icon runs showing the progress, but there's no information about the current state, and what
contributors are already loaded.

You can show the intermediate results earlier and display all the contributors after loading the data for each of the
repositories:

![Loading data](loading.gif)

To implement this functionality, pass the logic updating the UI as a callback, so that it's called on each intermediate
state:

```kotlin
suspend fun loadContributorsProgress(
    service: GitHubService,
    req: RequestData,
    updateResults: suspend (List<User>, completed: Boolean) -> Unit
) {
    // loading the data
    // calling `updateResults` on intermediate states
}
```

On the call site, pass the callback updating the results from the `Main` thread:

```kotlin
launch(Dispatchers.Default) {
    loadContributorsProgress(service, req) { users, completed ->
        withContext(Dispatchers.Main) {
            updateResults(users, startTime, completed)
        }
    }
}
```

The `updateResults` parameter is declared as `suspend` in `loadContributorsProgress()`. It's necessary to
call `withContext`, which is a `suspend` function inside the corresponding lambda argument.

`updateResults` callback takes an additional Boolean parameter as an argument saying whether all the loading completed
and the results are final.

#### Task

In the `Request6Progress.kt` file, implement the `loadContributorsProgress()` function that shows the intermediate
progress. Base it on the `loadContributorsSuspend` function from `Request4Suspend.kt`.

Use a simple version without concurrency; you'll add it later in the next section.

> The intermediate list of contributors should be shown in an "aggregated" state, not just the list of users loaded for
> each repository. The total numbers of contributions for each user should be increased when the data for each new
> repository is loaded.
>
{type="note"}

#### Solution {initial-collapse-state="collapsed"}

To store the intermediate list of loaded contributors in the "aggregated" state, define an `allUsers` variable which
stores the list of users, and then update it after contributors for each new repository are loaded:

```kotlin
suspend fun loadContributorsProgress(
    service: GitHubService,
    req: RequestData,
    updateResults: suspend (List<User>, completed: Boolean) -> Unit
) {
    val repos = service
        .getOrgRepos(req.org)
        .also { logRepos(req, it) }
        .bodyList()

    var allUsers = emptyList<User>()
    for ((index, repo) in repos.withIndex()) {
        val users = service.getRepoContributors(req.org, repo.name)
            .also { logUsers(repo, it) }
            .bodyList()

        allUsers = (allUsers + users).aggregate()
        updateResults(allUsers, index == repos.lastIndex)
    }
}
```

An `updateResults` callback is called after each request is completed:

![Progress on requests](progress.png)

The solution doesn't include concurrency so far. This code is sequential, so you don't need synchronization.

The best option would be to send requests concurrently and update the intermediate results after getting the response
for each repository:

![Concurrent requests](progress-and-concurrency.png)

To add concurrency, use _channels_.

## Channels

Writing code with a shared mutable state is quite difficult and error-prone (like in the solution using callbacks).
Sharing information by communication instead of using the common mutable state simplifies this.
Coroutines can communicate with each other through _channels_.

Channels are communication primitives that allow passing data between different coroutines. One coroutine can _send_
some information to a channel, while the other one can _receive_ this information from it:

![Using channels](using-channel.png)

A coroutine that sends (produces) information is often called a producer, and a coroutine that receives (consumes)
information is called a consumer. Coroutines can send information to the same channel, and coroutines can receive data
from it:

![Using channels with many-coroutines](using-channel-many-coroutines.png)

> When many coroutines receive information from the same channel, each element is handled only once by one of the
> consumers. Handling it means removing this element from the channel.
>
{type="note"}

You can think of a channel as similar to a collection of elements
(the direct analog would be a queue: elements are added to one end and received from another). However, there's an
important difference, unlike collections, even in their synchronized versions, a channel can _suspend_ `send()`
and `receive()` operations.

This happens when the channel is empty or full, in case the channel size might be constrained, and then it can be full.

`Channel` is represented with three different interfaces: `SendChannel`, `ReceiveChannel`, and `Channel` that extends
the first two. You usually create a channel and give it to producers as a `SendChannel` instance so that only they can
send it to it.
You give a channel to consumers as `ReceiveChannel` instance so that only they can receive from it. Both `send`
and `receive` methods are declared as `suspend`:

```kotlin
interface SendChannel<in E> {
    suspend fun send(element: E)
    fun close(): Boolean
}

interface ReceiveChannel<out E> {
    suspend fun receive(): E
}

interface Channel<E> : SendChannel<E>, ReceiveChannel<E>
```

The producer can close a channel to indicate that no more elements are coming.

Several types of channels are defined in the library. They differ in how many elements they can internally store and
whether the `send()` call can suspend or not.
For all the channel types, the `receive()` call behaves similarly: it receives an element if the channel is not empty
and otherwise suspends.

* **Unlimited channel**

![Unlimited channel](unlimited-channel.png)

An unlimited channel is the closest analog to a queue: producers can send elements to this channel, and it will grow
infinitely. The `send()` call will never be suspended.
If there's no more memory, you'll get an `OutOfMemoryException`.
The difference with a queue appears when a consumer tries to receive from an empty channel and gets suspended until some
new elements are sent.

* **Buffered channel**

![Buffered channel](buffered-channel.png)

The size of a buffered channel is constrained by the specified number.
Producers can send elements to this channel until the size limit is reached. All the elements are internally stored.
When the channel is full, the next `send` call on it suspends until more free space appears.

* **"Rendezvous" channel**

!["Rendezvous" channel](rendezvous-channel.png)

The "Rendezvous" channel is a channel without a buffer. It's the same as creating a buffered channel with a zero size.
One of the functions (`send()` or `receive()`) always gets suspended until the other is called.
If the `send` function is called and there's no suspended `receive` call ready to process the element, `send()`
suspends.
Similarly, if the `receive` function is called and the channel is empty or, in other words, there's no
suspended `send()` call ready to send the element, the `receive()` call suspends.
The "rendezvous" name ("a meeting at an agreed time and place") refers to the fact that `send()` and `receive()`
should "meet on time".

* **Conflated channel**

![Conflated channel](conflated-channel.gif)

A new element sent to the conflated channel will overwrite the previously sent element, so the receiver will always
get only the latest element. The `send()` call never suspends.

When you create a channel, you specify its type or the buffer size (if you need a buffered one):

```kotlin
val rendezvousChannel = Channel<String>()
val bufferedChannel = Channel<String>(10)
val conflatedChannel = Channel<String>(CONFLATED)
val unlimitedChannel = Channel<String>(UNLIMITED)
```

By default, a "Rendezvous" channel is created.

Create a "Rendezvous" channel, two producer coroutines, and a consumer coroutine:

```kotlin
import kotlinx.coroutines.channels.Channel
import kotlinx.coroutines.*

fun main() = runBlocking<Unit> {
    val channel = Channel<String>()
    launch {
        channel.send("A1")
        channel.send("A2")
        log("A done")
    }
    launch {
        channel.send("B1")
        log("B done")
    }
    launch {
        repeat(3) {
            val x = channel.receive()
            log(x)
        }
    }
}

fun log(message: Any?) {
    println("[${Thread.currentThread().name}] $message")
}
```

To get a better understanding, watch the following video:

![Video explaining the channels sample](https://youtu.be/HpWQUoVURWQ)

#### Task

Implement the function `loadContributorsChannels()` that requests all the GitHub contributors concurrently but shows
intermediate progress at the same time.

For this, use previous functions, `loadContributorsConcurrent()` from `Request5Concurrent.kt`
and `loadContributorsProgress()` from `Request6Progress.kt`.

#### Tip {initial-collapse-state="collapsed"}

Different coroutines that concurrently receive contributor lists for different repositories can send all the received
results to the same channel:

```kotlin
val channel = Channel<List<User>>()
for (repo in repos) {
    launch {
        val users = TODO()
        // ...
        channel.send(users)
    }
}
```

Then the elements from this channel can be received one by one and processed:

```kotlin
repeat(repos.size) {
    val users = channel.receive()
    // ...
}
```

Since the `receive()` calls are sequential, no additional synchronization is needed.

#### Solution {initial-collapse-state="collapsed"}

As with the `loadContributorsProgress()` function, you can create an `allUsers` variable to store the intermediate
states of the "all contributors" list.
Each new list received from the channel is added to the list of all users. You aggregate the result and update the state
using the `updateResults` callback:

```kotlin
suspend fun loadContributorsChannels(
    service: GitHubService,
    req: RequestData,
    updateResults: suspend (List<User>, completed: Boolean) -> Unit
) = coroutineScope {

    val repos = service
        .getOrgRepos(req.org)
        .also { logRepos(req, it) }
        .bodyList()

    val channel = Channel<List<User>>()
    for (repo in repos) {
        launch {
            val users = service.getRepoContributors(req.org, repo.name)
                .also { logUsers(repo, it) }
                .bodyList()
            channel.send(users)
        }
    }
    var allUsers = emptyList<User>()
    repeat(repos.size) {
        val users = channel.receive()
        allUsers = (allUsers + users).aggregate()
        updateResults(allUsers, it == repos.lastIndex)
    }
}
```

Results for different repositories are added to the channel as soon as they are ready. At first, when all the requests
are sent, and no data is received, the `receive()` call suspends. In this case, the whole "load contributors" coroutine
suspends.

Then, when the list of users is sent to the channel, the "load contributors" coroutine resumes, the `receive()` call
returns this list, and the results are immediately updated.

Note that neither coroutines nor channels will completely eradicate the complexity that comes from concurrency. Still,
they definitely make life easier when you need to reason it and understand what's going on.

## Testing coroutines

It'd be nice to test all solutions, ensure that the solution with concurrent coroutines is faster than the solution with
the `suspend` functions, and check that the solution with channels is faster than the simple "progress" one.

Have a look at how to compare the total running time of these solutions:

Mock a GitHub service and make this service return results after the given timeouts:

```
repos request - returns an answer within 1000 ms delay
repo-1 - 1000 ms delay
repo-2 - 1200 ms delay
repo-3 - 800 ms delay
```

2. Test that the sequential solution with the `suspend` functions should take around 4000 ms:

```
4000 = 1000 + (1000 + 1200 + 800)
```

And the concurrent solution should take around 2200 ms:

```
2200 = 1000 + max(1000, 1200, 800)
```

For the solutions showing progress, you can also check the intermediate results with timestamps.

The corresponding test data is defined in `test/contributors/testData.kt`, and the files `Request4SuspendKtTest`,
... `Request7ChannelsKtTest` contain the straightforward tests that use mock service calls.

However, there are two problems here:

* These tests take too long to run. Each test takes around 2 to 4 seconds, and you need to wait for the results each
  time. It's not very efficient.
* You can't rely on the exact time the solution runs because it still takes additional time to warm up and run the code
  etc.
  It's possible to add a constant, but then it will differ from a machine to a machine.

> The mock service delays should be higher than this constant, so you can see a difference. If the constant is 0.5 sec,
> making the delays 0.1 sec won't be enough.
>
{type="note"}

A better way is to use special frameworks to test the timing while running the same code several times (which increases
the total time even more), but it's complicated to learn and set up.

In this case, however, you need to test that solutions with provided test delays behave as expected, one faster than the
other.

To fix these problems, you can use _virtual_ time. For this, a special test dispatcher is used. It keeps track of the
virtual time passed from the start and runs everything immediately in real-time.

When you run coroutines on this dispatcher, the `delay` will return immediately and advance the virtual time.

The tests using this mechanism run fast, but you can still check what happens at different moments in virtual time. The
total running time drastically decreases:

![Comparison for total running time](time-comparison.png)

To make use of virtual time, replace the `runBlocking` invocation with a `runBlockingTest`. `runBlockingTest` takes an
extension lambda to `TestCoroutineScope` as an argument.
When you call `delay` in a `suspend` function inside this special scope, `delay` will increase the virtual time instead
of delaying in real-time:

```kotlin
@Test
fun testDelayInSuspend() = runBlockingTest {
    val realStartTime = System.currentTimeMillis() 
    val virtualStartTime = currentTime
        
    foo()
    println("${System.currentTimeMillis() - realStartTime} ms") // ~ 6 ms
    println("${currentTime - virtualStartTime} ms")             // 1000 ms
}

suspend fun foo() {
    delay(1000)    // auto-advances without delay
    println("foo") // executes eagerly when foo() is called
}
```

You can check the current virtual time using the `currentTime` property of `TestCoroutineScope`.

> The actual running time in this example is several milliseconds, while virtual time equals the delay argument, which
> is 1000 milliseconds.
>
{type="note"}

To enjoy the full effect of "virtual" `delay` in child coroutines,
start all the child coroutines with `TestCoroutineDispatcher`. Otherwise, it won't work. This dispatcher is
automatically inherited from the other `TestCoroutineScope`, unless you provide a different dispatcher:

```kotlin
@Test
fun testDelayInLaunch() = runBlockingTest {
    val realStartTime = System.currentTimeMillis()
    val virtualStartTime = currentTime

    bar()

    println("${System.currentTimeMillis() - realStartTime} ms") // ~ 11 ms
    println("${currentTime - virtualStartTime} ms")             // 1000 ms
}

suspend fun bar() = coroutineScope {
    launch {
        delay(1000)    // auto-advances without delay
        println("bar") // executes eagerly when bar() is called
    }
}
```

If `launch` is called with the context of `Dispatchers.Default` in the example above, the test will fail. You'll get an
exception saying that the job has not been completed yet.

You can test the `loadContributorsConcurrent` function this way only if it starts the child coroutines with the
inherited context, without modifying it using the `Dispatchers.Default` dispatcher.

You can specify the context elements like the dispatcher when _calling_ a function rather than when _defining_ it, which
is more flexible and easier to test.

> The testing API that supports virtual time is Experimental and may change in the future. By default, the compiler
> shows warnings if you use it.
>
{type="warning"}

To suppress these warnings:

Annotate the test function or the whole class containing the tests with `@OptIn(ExperimentalCoroutinesApi::class)`.
Add the compiler argument telling it that you're using the experimental API:

```kotlin
compileTestKotlin {
    kotlinOptions {
        freeCompilerArgs += "-Xuse-experimental=kotlin.Experimental"
    }
}
```

In the project corresponding to this tutorial it's already been added to the Gradle script.

#### Task

Refactor all the following tests in `tests/tasks/` to use virtual time instead of real-time:

```
Request4SuspendKtTest.kt
Request5ConcurrentKtTest.kt
Request6ProgressKtTest.kt
Request7ChannelsKtTest.kt
```

Compare the total running time with the time before this refactoring.

#### Tip {initial-collapse-state="collapsed"}

Replace `runBlocking` invocation with `runBlockingTest`, and
`System.currentTimeMillis()` with `currentTime`:

```kotlin
@Test
fun test() = runBlockingTest {
    val startTime = currentTime
    // action
    val totalTime = currentTime - startTime
    // testing result
}
```

Uncomment the assertions checking the exact virtual time.
Don't forget to add `@UseExperimental(ExperimentalCoroutinesApi::class)`.

#### Solution {initial-collapse-state="collapsed"}

Here's the solution for the concurrent case:

```kotlin
fun testConcurrent() = runBlockingTest {
    val startTime = currentTime
    val result = loadContributorsConcurrent(MockGithubService, testRequestData)
    Assert.assertEquals("Wrong result for 'loadContributorsConcurrent'", expectedConcurrentResults.users, result)
    val totalTime = currentTime - startTime

    Assert.assertEquals(
        "The calls run concurrently, so the total virtual time should be 2200 ms: " +
                "1000 for repos request plus max(1000, 1200, 800) = 1200 for concurrent contributors requests)",
        expectedConcurrentResults.timeFromStart, totalTime
    )
}
```

First, you check that the results are available exactly at the expected virtual time, and then you check the results
themselves:

```kotlin
fun testChannels() = runBlockingTest {
    val startTime = currentTime
    var index = 0
    loadContributorsChannels(MockGithubService, testRequestData) { users, _ ->
        val expected = concurrentProgressResults[index++]
        val time = currentTime - startTime
        Assert.assertEquals(
            "Expected intermediate results after ${expected.timeFromStart} ms:",
            expected.timeFromStart, time
        )
        Assert.assertEquals("Wrong intermediate results after $time:", expected.users, users)
    }
}
```

The first intermediate result for the last version with channels is available sooner than the progress version, and you
can see the difference in tests using virtual time.

The tests for the remaining "suspend" and "progress" tasks are very similar; you can find them in the project '
solutions' branch.

## What's next

Find out more about using [virtual time and experimental testing package](https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-test/).