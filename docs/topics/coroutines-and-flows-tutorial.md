<contribute-url>https://github.com/Kotlin/kotlinx.coroutines/edit/master/docs/topics/</contribute-url>

[//]: # (title: Coroutines and flows – tutorial)

<web-summary>Learn how to use Kotlin coroutines and flows in a step-by-step tutorial.</web-summary>

Learn how to use Kotlin coroutines and flows by completing this hands-on tutorial in IntelliJ IDEA.

> No prior knowledge of coroutines is required, but you should be familiar with basic Kotlin syntax.
>
> If you're new to Kotlin, we recommend completing the [Kotlin tour](kotlin-tour-welcome.md) first.
>
{style="tip"}

Throughout this tutorial, you'll work on an application that loads articles and their comments from a local server.
As you progress, you'll implement different loading strategies and use each one to explore a new aspect of Kotlin coroutines and flows.
By the end, the application will load data concurrently, report progress, support cancellation, and handle failures while keeping the UI responsive.

To implement these loading strategies, you'll progress through the following steps:

<p>
   <img src="icon-1.svg" width="20" alt="First step"/> <a href="coroutines-tutorial-blocking-requests.md">Replace blocking calls with suspending functions</a><br/>
   <img src="icon-2.svg" width="20" alt="Second step"/> <a href="coroutines-tutorial-concurrent-loading.md">Load articles concurrently</a><br/>
   <img src="icon-3.svg" width="20" alt="Third step"/> <a href="coroutines-tutorial-cancel-coroutines.md">Cancel concurrent loading with structured concurrency</a><br/>
   <img src="icon-4.svg" width="20" alt="Fourth step"/> <a href="coroutines-tutorial-loading-progress-with-flow.md">Show loading progress with a flow</a><br/>
   <img src="icon-5.svg" width="20" alt="Fifth step"/> <a href="concurrent-progress.md">Emit concurrent results with channelFlow()</a><br/>
   <img src="icon-6.svg" width="20" alt="Sixth step"/> <a href="flow-failures.md">Handle exceptions while loading articles</a><br/>
</p>

## Before you start

Complete the following before starting the tutorial:

1. Download and install the latest version of [IntelliJ IDEA](https://www.jetbrains.com/idea/download/).
2. Make sure that JDK 17 or later is installed and configured for Gradle.
3. Clone the [project template](https://github.com/kotlin-hands-on/intro-coroutines-flows) by selecting **File | New | Project from Version Control** in IntelliJ IDEA and using this URL:

   ```text
   https://github.com/kotlin-hands-on/intro-coroutines-flows
   ```
   
4. Check out the `main` branch, which contains the unfinished tasks.

### Explore the project

The `desktop-client/src/jvmMain/kotlin/org/example/articles/tasks` directory contains the task files you'll work with throughout the tutorial.
In these files, you'll find the `TODO()` placeholders to complete.

![The coroutines and flows tutorial project structure ](coroutines-tutorial-project-structure.png){width="700"}

You won't modify the following directories, but you can inspect them to understand how the application and tests work:

* `desktop-client/src/jvmMain/kotlin/org/example/articles/ui` contains the Compose UI and the view model that calls your task functions.
* `desktop-client/src/jvmMain/kotlin/org/example/articles/network` contains the blocking and suspending clients for loading articles and comments.
* `desktop-client/src/jvmTest/kotlin/org/example/articles/data` contains the mock service and expected results used by the tests.
* `server` contains the local Ktor server and the simulated delays and failures.
* `shared` contains the article data and local server configuration shared by the client and server.

You can find solutions for all the tasks on the `solutions` branch of the [project's repository](https://github.com/kotlin-hands-on/intro-coroutines-flows/tree/solutions).

### Run the application

Before running the application, make sure that port `9020` is available for the local server.

1. Select the **Articles** run configuration in IntelliJ IDEA, and click **Run** ![Run icon](run-icon.png){width=20}{type="joined"}:

   ![Select the `articles` run configuration, and click run](run-articles-app.png){width="600"}

   Alternatively, run the application from the command line with the following:

    ```bash
    ./gradlew :desktop-client:jvmRun -DmainClass=org.example.articles.ArticlesMainKt
    ```

2. Wait for the local server to start. When it's ready, the article browser appears in the application window.

As you complete each task, select the corresponding option from the **Loading Mode** menu to see how your implementation behaves:

![The Articles application with the Loading Mode menu](articles-app.png){width="700"}

## Next step

<list id="tour-nav">
  <li>
    <a as="button" href="coroutines-tutorial-blocking-requests.md" mode="classic" icon="arrow-right" icon-position="right">Next step</a>
  </li>
</list>