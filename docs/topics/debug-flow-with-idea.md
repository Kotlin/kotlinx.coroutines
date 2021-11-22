[//]: # (title: Debug Kotlin Flow using IntelliJ IDEA – tutorial)

This tutorial demonstrates how to create Kotlin Flow and debug it using IntelliJ IDEA.

The tutorial assumes you have prior knowledge of the [coroutines](coroutines-guide.md) and [Kotlin Flow](flow.md#flows) concepts.

> Debugging works for `kotlinx-coroutines-core` version 1.3.8 or later.
>
{type="note"}

## Create a Kotlin flow

Create a Kotlin [flow](https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/flow.html) with a slow emitter and a slow collector:

1. Open a Kotlin project in IntelliJ IDEA. If you don't have a project, [create one](jvm-get-started.md#create-an-application).

2. Open the `main.kt` file in `src/main/kotlin`.

    The `src` directory contains Kotlin source files and resources. The `main.kt` file contains sample code that will print `Hello World!`.

2. Create the `simple()` function that returns a flow of three numbers:

    * Use the [`delay()`](https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/delay.html) function to imitate CPU-consuming blocking code. It suspends the coroutine for 100 ms without blocking the thread.
    * Produce the values in the `for` loop using the [`emit()`](https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/-flow-collector/emit.html) function.

    ```kotlin
    import kotlinx.coroutines.*
    import kotlinx.coroutines.flow.*
    import kotlin.system.*
 
    fun simple(): Flow<Int> = flow {
        for (i in 1..3) {
            delay(100)
            emit(i)
        }
    }
    ```

3. Change the code in the `main()` function:

    * Use the [`runBlocking()`](https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/run-blocking.html) block to wrap a coroutine.
    * Collect the emitted values using the [`collect()`](https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/collect.html) function.
    * Use the [`delay()`](https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/delay.html) function to imitate CPU-consuming code. It suspends the coroutine for 300 ms without blocking the thread.
    * Print the collected value from the flow using the [`println()`](https://kotlinlang.org/api/latest/jvm/stdlib/stdlib/kotlin.io/println.html) function.

    ```kotlin
    fun main() = runBlocking {
        simple()
            .collect { value ->
                delay(300)
                println(value)
            }
    }
    ```

4. Build the code by clicking **Build Project**.

    ![Build an application](flow-build-project.png)

## Debug the coroutine

1. Set a breakpoint at the line where the `emit()` function is called:

    ![Build a console application](flow-breakpoint.png)

2. Run the code in debug mode by clicking **Debug** next to the run configuration at the top of the screen.

    ![Build a console application](flow-debug-project.png)

    The **Debug** tool window appears: 
    * The **Frames** tab contains the call stack.
    * The **Variables** tab contains variables in the current context. It tells us that the flow is emitting the first value.
    * The **Coroutines** tab contains information on running or suspended coroutines.

    ![Debug the coroutine](flow-debug-1.png)

3. Resume the debugger session by clicking **Resume Program** in the **Debug** tool window. The program stops at the same breakpoint.

    ![Debug the coroutine](flow-resume-debug.png)

    Now the flow emits the second value.

    ![Debug the coroutine](flow-debug-2.png)

## Add a concurrently running coroutine

1. Open the `main.kt` file in `src/main/kotlin`.

2. Enhance the code to run the emitter and collector concurrently:

    * Add a call to the [`buffer()`](https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/buffer.html) function to run the emitter and collector concurrently. `buffer()` stores emitted values and runs the flow collector in a separate coroutine. 
 
    ```kotlin
    fun main() = runBlocking<Unit> {
        simple()
            .buffer()
            .collect { value ->
                delay(300)
                println(value)
            }
    }
    ```

4. Build the code by clicking **Build Project**.

## Debug a Kotlin flow with two coroutines

1. Set a new breakpoint at `println(value)`.

2. Run the code in debug mode by clicking **Debug** next to the run configuration at the top of the screen.

    ![Build a console application](flow-debug-3.png)

    The **Debug** tool window appears.

    In the **Coroutines** tab, you can see that there are two coroutines running concurrently. The flow collector and emitter run in separate coroutines because of the `buffer()` function.
    The `buffer()` function buffers emitted values from the flow.
    The emitter coroutine has the **RUNNING** status, and the collector coroutine has the **SUSPENDED** status.

2. Resume the debugger session by clicking **Resume Program** in the **Debug** tool window.

    ![Debugging coroutines](flow-debug-4.png)

    Now the collector coroutine has the **RUNNING** status, while the emitter coroutine has the **SUSPENDED** status.

    You can dig deeper into each coroutine to debug your code.