[//]: # (title: Debug coroutines using IntelliJ IDEA – tutorial)

This tutorial demonstrates how to create Kotlin coroutines and debug them using IntelliJ IDEA.

The tutorial assumes you have prior knowledge of the [coroutines](coroutines-guide.md) concept.

## Create coroutines

1. Open a Kotlin project in IntelliJ IDEA. If you don't have a project, [create one](jvm-get-started.md#create-a-project).
2. To use the `kotlinx.coroutines` library in a Gradle project, add the following dependency to `build.gradle(.kts)`:

   <tabs group="build-script">
   <tab title="Kotlin" group-key="kotlin">

   ```kotlin
   dependencies {
       implementation("org.jetbrains.kotlinx:kotlinx-coroutines-core:%coroutinesVersion%")
   }
   ``` 

   </tab>
   <tab title="Groovy" group-key="groovy">
   
   ```groovy
   dependencies {
       implementation 'org.jetbrains.kotlinx:kotlinx-coroutines-core:%coroutinesVersion%'
   }
   ```
   
   </tab>
   </tabs>

   For other build systems, see instructions in the [`kotlinx.coroutines` README](https://github.com/Kotlin/kotlinx.coroutines#using-in-your-projects).
   
3. Open the `Main.kt` file in `src/main/kotlin`.

    The `src` directory contains Kotlin source files and resources. The `Main.kt` file contains sample code that will print `Hello World!`.

4. Change code in the `main()` function:

    * Use the [`runBlocking()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/run-blocking.html) block to wrap a coroutine.
    * Use the [`async()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/async.html) function to create coroutines that compute deferred values `a` and `b`.
    * Use the [`await()`](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-deferred/await.html) function to await the computation result.
    * Use the [`println()`](https://kotlinlang.org/api/latest/jvm/stdlib/kotlin.io/println.html) function to print computing status and the result of multiplication to the output.

    ```kotlin
    import kotlinx.coroutines.*
    
    fun main() = runBlocking<Unit> {
        val a = async {
            println("I'm computing part of the answer")
            6
        }
        val b = async {
            println("I'm computing another part of the answer")
            7
        }
        println("The answer is ${a.await() * b.await()}")
    }
    ```

5. Build the code by clicking **Build Project**.

    ![Build an application](flow-build-project.png)

## Debug coroutines

1. Set breakpoints at the lines with the `println()` function call:

    ![Build a console application](coroutine-breakpoint.png)

2. Run the code in debug mode by clicking **Debug** next to the run configuration at the top of the screen.

    ![Build a console application](flow-debug-project.png)

    The **Debug** tool window appears: 
    * The **Frames** tab contains the call stack.
    * The **Variables** tab contains variables in the current context.
    * The **Coroutines** tab contains information on running or suspended coroutines. It shows that there are three coroutines.
    The first one has the **RUNNING** status, and the other two have the **CREATED** status.

    ![Debug the coroutine](coroutine-debug-1.png)

3. Resume the debugger session by clicking **Resume Program** in the **Debug** tool window:

    ![Debug the coroutine](coroutine-debug-2.png)
    
    Now the **Coroutines** tab shows the following:
    * The first coroutine has the **SUSPENDED** status – it is waiting for the values so it can multiply them.
    * The second coroutine is calculating the `a` value – it has the **RUNNING** status.
    * The third coroutine has the **CREATED** status and isn’t calculating the value of `b`.

4. Resume the debugger session by clicking **Resume Program** in the **Debug** tool window:

    ![Build a console application](coroutine-debug-3.png)

    Now the **Coroutines** tab shows the following:
    * The first coroutine has the **SUSPENDED** status – it is waiting for the values so it can multiply them.
    * The second coroutine has computed its value and disappeared.
    * The third coroutine is calculating the value of `b` – it has the **RUNNING** status.

> You can disable a "was optimised out" feature via the `-Xdebug` compiler option.
> The "was optimised out" feature optimizes variables when you use suspend functions.
> However, debugging a code with optimized variables is hard because you don't see their values.
> Be careful: disabling this feature via `-Xdebug` can [cause memory leaks](https://youtrack.jetbrains.com/issue/KT-48678/Coroutine-debugger-disable-was-optimised-out-compiler-feature#focus=Comments-27-6015585.0-0).
>
{type="tip"}

Using IntelliJ IDEA debugger, you can dig deeper into each coroutine to debug your code.
