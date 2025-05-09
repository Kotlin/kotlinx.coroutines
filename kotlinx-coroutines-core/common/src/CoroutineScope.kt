@file:OptIn(ExperimentalContracts::class)
@file:Suppress("LEAKED_IN_PLACE_LAMBDA", "WRONG_INVOCATION_KIND")

package kotlinx.coroutines

import kotlinx.coroutines.internal.*
import kotlinx.coroutines.intrinsics.*
import kotlin.contracts.*
import kotlin.coroutines.*
import kotlin.coroutines.intrinsics.*

/**
 * A scope in which coroutines run.
 *
 * A scope defines a group of coroutines with shared execution properties
 * (represented as [CoroutineContext.Element] values)
 * and mutually dependent lifecycles.
 *
 * The execution properties of coroutines are defined by the [coroutineContext] property of this interface
 * and are inherited by all coroutines launched in this scope.
 * For example, the [CoroutineDispatcher] element of the context defines which threads the coroutines will run on,
 * with [Dispatchers.Main] meaning the coroutines will run on the main thread of the application.
 * See a more detailed explanation of the context elements in a separate section below.
 *
 * The lifecycles of coroutines are governed by a set of rules called "structured concurrency",
 * meaning that the lifetimes of child coroutines are strictly inside the lifetime of the scope.
 * If the scope is cancelled, all coroutines in it are cancelled too, and the scope itself
 * cannot be completed until all its children are completed.
 * See a more detailed explanation of structured concurrency in a separate section below.
 *
 * ## Using the coroutine scope
 *
 * The methods of this interface are not intended to be called directly.
 * Instead, a [CoroutineScope] is passed as a receiver to the coroutine builders such as [launch] and [async],
 * controlling the execution properties and lifetimes of the created coroutines.
 *
 * ## Coroutine context elements
 *
 * A [CoroutineScope] is defined by a set of [CoroutineContext] elements, one of which is typically a [Job],
 * described in the section on structured concurrency and responsible for managing lifetimes of coroutines.
 *
 * Other coroutine context elements include, but are not limited to, the following:
 *
 * - The scheduling policy, represented by a [CoroutineDispatcher] element.
 *   Some commonly used dispatchers are provided in the [Dispatchers] object.
 * - [CoroutineExceptionHandler] that defines how failures of child coroutines should be reported whenever
 *   structured concurrency does not provide a way to propagate the failure to the parent
 *   (that is, a [SupervisorJob] is used).
 * - A [CoroutineName] element that can be used to name coroutines for debugging purposes.
 * - On the JVM, a `ThreadContextElement` ensures that a specific thread-local value gets set on the thread
 *   that executes the coroutine.
 *
 * ## Obtaining a coroutine scope
 *
 * Manual implementations of this interface are not recommended.
 * Instead, there are several structured ways to obtain a [CoroutineScope].
 *
 * ### Lexical scopes
 *
 * [coroutineScope] and [supervisorScope] functions can be used in any `suspend` function to define a scope
 * lexically, ensuring that all coroutines launched in this scope have completed by the time scope-limiting
 * function exits.
 *
 * ```
 * suspend fun doSomething() = coroutineScope { // scope `A`
 *     repeat(5) { outer ->
 *         // spawn a new coroutine in the scope `A`
 *         launch {
 *             println("Coroutine $outer started")
 *             coroutineScope { // scope `B`, separate for each `outer` coroutine
 *                 repeat(5) { inner ->
 *                     // spawn a new coroutine in the scope `B`
 *                     launch {
 *                         println("Coroutine $outer.$inner started")
 *                         delay(10.milliseconds)
 *                         println("Coroutine $outer.$inner finished")
 *                     }
 *                 }
 *             }
 *             // will only exit once all `Coroutine $outer.X finished` messages are printed
 *             println("Coroutine $outer finished")
 *         }
 *     }
 * } // will only exit once all `Coroutine X finished` messages are printed
 * ```
 *
 * This should be the preferred way to create a scope for coroutines.
 *
 * ### `CoroutineScope` constructor function
 *
 * When the lifecycle of the scope is not limited lexically
 * (for example, when coroutines should outlive the function that creates them)
 * but is tied to the lifecycle of some entity, the [CoroutineScope] constructor function can be used
 * to define a personal scope for that entity that should be stored as a field there.
 *
 * **The key part of using a custom `CoroutineScope` is cancelling it at the end of the lifecycle.**
 * The [CoroutineScope.cancel] extension function shall be used when the entity launching coroutines
 * is no longer needed. It cancels all the coroutines that might still be running on its behalf.
 *
 * ```
 * class MyEntity(scope: CoroutineScope? = null): AutoCloseable {
 *    // careful: do not write `get() =` here by accident!
 *    private val scope = scope ?: CoroutineScope(SupervisorJob() + CoroutineExceptionHandler { _, e ->
 *        println("Error in coroutine: $e")
 *    })
 *
 *    fun doSomethingWhileEntityExists() = scope.launch {
 *        while (true) {
 *            // do some work
 *            delay(50.milliseconds)
 *            println("Doing something")
 *        }
 *    }
 *
 *    override fun close() {
 *        // cancel all computations related to this entity
 *        scope.cancel()
 *    }
 * }
 *
 * fun main() {
 *     MyEntity().use { entity ->
 *         entity.doSomethingWhileEntityExists()
 *         Thread.sleep(200)
 *         entity.close()
 *     }
 * }
 * ```
 *
 * Usually, a custom [CoroutineScope] should be created with a [SupervisorJob] and
 * a [CoroutineExceptionHandler] to handle exceptions in child coroutines.
 * See the documentation for the [CoroutineScope] constructor function for more details.
 * Also note that `MyEntity` accepts the `scope` parameter that can be used to pass a custom scope for testing.
 *
 * Sometimes, authors of coroutine-aware frameworks provide [CoroutineScope] instances like this out of the box.
 * For example, on Android, all entities with a lifecycle and all `ViewModel` instances expose a [CoroutineScope]:
 * see [the corresponding documentation](https://developer.android.com/topic/libraries/architecture/coroutines).
 *
 * ### Taking another view of an existing scope
 *
 * Occasionally, several coroutines need to be launched with the same additional [CoroutineContext] that is not
 * present in the original scope.
 * In this case, the [CoroutineScope.plus] operator can be used to create a new view of the existing scope:
 *
 * ```
 * coroutineScope {
 *     val sameScopeButInUiThread = this + Dispatchers.Main
 *     sameScopeButInUiThread.launch {
 *         println("Running on the main thread")
 *     }
 *     launch {
 *         println("This will run using the original dispatcher")
 *     }
 *     sameScopeButInUiThread.launch {
 *         println("And this will also run on the main thread")
 *     }
 * }
 * ```
 *
 * The lifecycle of the new scope is the same as the original one, but the context includes new elements.
 *
 * ### Application lifecycle scope
 *
 * [GlobalScope] is a [CoroutineScope] that has the lifetime of the whole application.
 * It is convenient for launching top-level coroutines that are not tied to the lifecycle of any entity,
 * but it is easy to misuse it and create memory leaks or resource leaks when a coroutine actually should be tied
 * to the lifecycle of some entity.
 *
 * ```
 * GlobalScope.launch(CoroutineExceptionHandler { _, e ->
 *     println("Error in coroutine: $e")
 * }) {
 *    while (true) {
 *        println("I will be running forever, you cannot stop me!")
 *        delay(1.seconds)
 *    }
 * }
 * ```
 *
 * ### `by`-delegation
 *
 * When all else fails and a custom [CoroutineScope] implementation is needed, it is recommended to use
 * `by`-delegation to implement the interface:
 *
 * ```
 * class MyEntity : CoroutineScope by CoroutineScope(SupervisorJob() + Dispatchers.Main)
 * ```
 *
 * ## Structured concurrency in detail
 *
 * ### Overview
 *
 * *Structured concurrency* is an approach to concurrent programming that attempts to clarify the lifecycles of
 * concurrent operations and to make them easier to reason about.
 *
 * Skim the following motivating example:
 *
 * ```
 * suspend fun downloadFile(url: String): ByteArray {
 *     return withContext(Dispatchers.IO) {
 *         // this code will execute on the UI thread
 *         val file = byteArrayOf()
 *         // download the file
 *         return file
 *     }
 * }
 *
 * suspend fun downloadAndCompareTwoFiles() {
 *     coroutineScope {
 *         val file1 = async {
 *             // if this fails, everything else quickly fails too
 *             downloadFile("http://example.com/file1")
 *         }
 *         val file2 = async {
 *             downloadFile("http://example.com/file2")
 *         }
 *         launch(Dispatchers.Main) {
 *             // create a separate coroutine on the UI thread
 *             if (file1.await() == file2.await()) {
 *                 uiShow("Files are equal")
 *             } else {
 *                 uiShow("Files are not equal")
 *             }
 *         }
 *     }
 *     // this line will only run once all the coroutines created above
 *     // finish their work or get cancelled
 * }
 * ```
 *
 * In this example, two asynchronous operations are launched in parallel to download two files.
 * If one of the files fails to download, the other one is cancelled too, and the whole operation fails.
 * The `coroutineScope` function will not return until all the coroutines inside it are completed or cancelled.
 * In addition, it is possible to cancel the coroutine calling `downloadAndCompareTwoFiles`, and all the coroutines
 * inside it will be cancelled too.
 *
 * Without structured concurrency, ensuring that no resource leaks occur by the end of the operation and that
 * the operation responds promptly to failure and cancellation requests is challenging.
 * With structured concurrency, this orchestration is done automatically by the coroutine library,
 * and it is enough to specify the relationships between operations declaratively, as shown in the example,
 * without being overwhelmed by intricate inter-thread communications.
 *
 * ### Specifics
 *
 * Coroutines and [CoroutineScope] instances have an associated lifecycle.
 * A runtime representation of a lifecycle in `kotlinx.coroutines` called a [Job].
 * [Job] instances form a hierarchy of parent-child relationships,
 * and the [Job] of every coroutine spawned in a [CoroutineScope] is a child of the [Job] of that scope.
 * This is often shortened to saying that the coroutine is the scope's child.
 *
 * See the [Job] documentation for a detailed explanation of the lifecycle stages.
 *
 * ```
 * coroutineScope {
 *     val job = coroutineContext[Job]
 *     val childJob = launch { }
 *     check(job === childJob.parent)
 * }
 * ```
 *
 * Because every coroutine has a lifecycle and a [Job], a [CoroutineScope] can be associated with it.
 * Most coroutine builders in `kotlinx.coroutines` expose the [CoroutineScope] of the coroutine on creation:
 *
 * ```
 * coroutineScope { // this block has a `CoroutineScope` receiver
 *     val parentScope = this
 *     var grandChildFinished = false
 *     val childJob = launch {
 *         // this block has a `CoroutineScope` receiver too
 *         val childScope = this
 *         check(childScope.coroutineContext[Job]?.parent
 *             === parentScope.coroutineContext[Job])
 *         launch {
 *             // This block also has a `CoroutineScope` receiver!
 *             val grandChildScope = this
 *             check(grandChildScope.coroutineContext[Job]?.parent
 *                 === childScope.coroutineContext[Job])
 *             delay(100.milliseconds)
 *             grandChildFinished = true
 *         }
 *         // Because the grandchild coroutine
 *         // is a child of the child coroutine,
 *         // the child coroutine will not complete
 *         // until the grandchild coroutine does.
 *     }
 *     // Await completion of the child coroutine,
 *     // and therefore the grandchild coroutine too.
 *     childJob.join()
 *     check(grandChildFinished)
 * }
 * ```
 *
 * Such a [CoroutineScope] receiver is provided for [launch], [async], and other coroutine builders,
 * as well as for scoping functions like [coroutineScope], [supervisorScope], and [withContext].
 * Each of these [CoroutineScope] instances is tied to the lifecycle of the code block it runs in.
 *
 * Like the example above shows, a coroutine does not complete until all its children are completed.
 * This means that [Job.join] on a [launch] or [async] result or [Deferred.await] on an [async] result
 * will not return until all the children of that coroutine are completed,
 * and scoping functions like [coroutineScope] and [withContext] will not return until all the coroutines
 * launched in them are completed.
 *
 * #### Interactions between coroutines
 *
 * See the [Job] documentation for a detailed explanation of interactions between [Job] values.
 * Below is a summary of the most important points for structuring code in day-to-day usage.
 *
 * A coroutine cannot reach the final state until all its children have reached their final states.
 * See the example above.
 *
 * If a [CoroutineScope] is cancelled (either explicitly or because it corresponds to some coroutine that failed
 * with an exception), all its children are cancelled too:
 *
 * ```
 * val scope = CoroutineScope(
 *     SupervisorJob() + CoroutineExceptionHandler { _, e -> }
 * )
 * val job = scope.launch {
 *      // this coroutine will be cancelled
 *      awaitCancellation()
 * }
 * scope.cancel() // comment this out for the line below to hang
 * job.join() // finishes normally
 * ```
 *
 * If a coroutine fails with an exception *and* its parent is a normal [Job] (not a [SupervisorJob]),
 * the parent fails with that exception, too:
 *
 * ```
 * check(
 *     runCatching {
 *         coroutineScope {
 *             launch { throw IllegalStateException() }
 *             launch {
 *                 // this coroutine will be cancelled
 *                 // when the parent gets cancelled
 *                 awaitCancellation()
 *             }
 *         }
 *     }.exceptionOrNull()
 *     is IllegalStateException
 * )
 * ```
 *
 * Child jobs can lead to the failure of the parent even if the parent has already finished its work
 * and was ready to return a value:
 *
 * ```
 * val deferred = GlobalScope.async {
 *     launch {
 *         delay(100.milliseconds)
 *         throw IllegalStateException()
 *     }
 *     10 // this value will be lost!
 * }
 * check(
 *     runCatching { deferred.await() }.exceptionOrNull()
 *     is IllegalStateException
 * )
 * ```
 *
 * If a coroutine fails with an exception and its parent is a [SupervisorJob],
 * the parent is not cancelled (and therefore, the other children are also not affected),
 * but the failure is reported through other channels.
 * See [CoroutineExceptionHandler] for details.
 *
 * ### How-to: stop failures of child coroutines from cancelling other coroutines
 *
 * If not affecting the [CoroutineScope] on a failure in a child coroutine is the desired behaviour,
 * then a [SupervisorJob] should be used instead of [Job] when constructing the scope:
 *
 * ```
 * val scope = CoroutineScope(SupervisorJob() + Dispatchers.Main + CoroutineExceptionHandler { _, e ->
 *     println("Coroutine failed with exception $e")
 * })
 * val failingCoroutine = scope.launch(Dispatchers.IO) {
 *     throw IllegalStateException("This exception will not cancel the scope")
 * }
 * failingCoroutine.join()
 * scope.launch(Dispatchers.IO) {
 *     println("This coroutine is active! See: ${isActive}")
 * }
 * ```
 *
 * Likewise, [supervisorScope] can replace [coroutineScope]:
 *
 * ```
 * supervisorScope {
 *     val failingCoroutine = scope.launch(Dispatchers.IO + CoroutineExceptionHandler { _, e ->
 *         println("Coroutine failed with exception $e")
 *     }) {
 *         throw IllegalStateException("This exception will not cancel the scope")
 *     }
 *     failingCoroutine.join()
 *     launch(Dispatchers.IO) {
 *         println("This coroutine is active! See: ${isActive}")
 *     }
 * }
 * ```
 *
 * ### How-to: prevent a child coroutine from being cancelled
 *
 * Sometimes, you may want to run a coroutine even if the parent coroutine is cancelled.
 * This pattern provides a way to achieve that:
 *
 * ```
 * scope.launch(start = CoroutineStart.ATOMIC) {
 *     // Do not move `NonCancellable` to the `context` argument of `launch`!
 *     withContext(NonCancellable) {
 *         // This code will run even if the parent coroutine is cancelled
 *     }
 * }
 * ```
 *
 * [CoroutineStart.ATOMIC] ensures that the new coroutine is not cancelled until it is started.
 * [NonCancellable] in [withContext] ensures that the code inside the block is executed even if the coroutine
 * created by [launch] is cancelled.
 */
public interface CoroutineScope {
    /**
     * The context of this scope.
     *
     * The context represents various execution properties of the coroutines launched in this scope,
     * such as the [dispatcher][CoroutineDispatcher] or
     * the [procedure for handling uncaught exceptions][CoroutineExceptionHandler].
     * Except [GlobalScope], a [job][Job] instance for enforcing structured concurrency
     * must also be present in the context of every [CoroutineScope].
     * See the documentation for [CoroutineScope] for details.
     *
     * Accessing this property in general code is not recommended for any purposes
     * except accessing the [Job] instance for advanced usages.
     */
    public val coroutineContext: CoroutineContext
}

/**
 * Creates a new view of `this` [CoroutineScope], but with the specified [context] added to it.
 *
 * This is a shorthand for `CoroutineScope(thisScope.coroutineContext + context)` and can be used as
 * a combinator with existing constructors:
 * ```
 * val myApplicationLifetimeScope = GlobalScope + CoroutineExceptionHandler { _, e ->
 *     myLogger.error("Error in coroutine: $e")
 * }
 * ```
 *
 * **Pitfall**: if [context] contains a [Job], the new job will override the existing one in the scope.
 * This means that in terms of structured concurrency, the new scope will be unrelated to the old one.
 * Because of backward compatibility guarantees, [plus] does not check for this case, even though
 * it is a source of bugs.
 */
public operator fun CoroutineScope.plus(context: CoroutineContext): CoroutineScope =
    ContextScope(coroutineContext + context)

/**
 * Creates the a [CoroutineScope] for scheduling UI updates.
 *
 * Example of use:
 * ```
 * class MyAndroidActivity: Activity() {
 *     // be careful not to write `get() =` here by accident!
 *     private val scope = MainScope() + CoroutineExceptionHandler { _, e ->
 *         log("Unhandled error in coroutine: $e")
 *     }
 *
 *     fun updateProgressBar(newValue: Int) = scope.launch {
 *         // this coroutine will run on the main thread
 *         // ...
 *     }
 *
 *     override fun onDestroy() {
 *         super.onDestroy()
 *         scope.cancel()
 *     }
 * }
 * ```
 *
 * The new scope has [Dispatchers.Main] in its context, meaning that all coroutines launched in it
 * will run on the main thread.
 * It also has a [SupervisorJob] in its context, meaning that if one of the child coroutines fails,
 * the other coroutines will not be affected.
 * A [CoroutineExceptionHandler] is not installed.
 *
 * The resulting scope has [SupervisorJob] and [Dispatchers.Main] context elements.
 * If you want to append additional elements to the main scope, use the [CoroutineScope.plus] operator:
 * `val scope = MainScope() + CoroutineName("MyActivity")`.
 *
 * **Pitfall**: by default, this scope does not include a [CoroutineExceptionHandler], but uses a [SupervisorJob].
 * Together, this means that if a child coroutine created with [launch ]fails with an exception,
 * the failure will be reported in a platform-specific manner (e.g., a crash on Android).
 * Always supply a [CoroutineExceptionHandler] to [MainScope] using the [plus] operator if there is a chance
 * that a child coroutine may fail with an exception,
 * or use [async] instead of [launch] to have the consumer of the result handle the exception.
 *
 * **Pitfall**: there is no memoization of the [CoroutineScope] instance in this function.
 * Every call to this function creates a new instance of [MainScope], with an unrelated [SupervisorJob].
 * For example, writing `MainScope().cancel()` is meaningless,
 * because the only job that will be cancelled is the one created in that specific `MainScope()` call.
 */
@Suppress("FunctionName")
public fun MainScope(): CoroutineScope = ContextScope(SupervisorJob() + Dispatchers.Main)

/**
 * Returns `true` when the [Job] of this [CoroutineScope] is still active (has not completed and was not cancelled yet).
 *
 * Coroutine cancellation [is cooperative](https://kotlinlang.org/docs/cancellation-and-timeouts.html#cancellation-is-cooperative),
 * and usually, it's checked if a coroutine is cancelled when it *suspends*, for example,
 * when trying to read from a [channel][kotlinx.coroutines.channels.Channel] that is empty.
 *
 * Sometimes, a coroutine does not need to perform suspending operations but still wants to be cooperative
 * and respect cancellation.
 *
 * The [isActive] property is intended to be used for scenarios like this:
 * ```
 * val watchdogDispatcher = Dispatchers.IO.limitParallelism(1)
 * fun backgroundWork() {
 *     println("Doing bookkeeping in the background in a blocking manner")
 *     Thread.sleep(100L) // Sleep 100ms
 * }
 * // Part of some non-trivial CoroutineScope-confined lifecycle
 * launch(watchdogDispatcher) {
 *     while (isActive) {
 *         // Repetitively do some background work that is non-suspending
 *         backgroundWork()
 *     }
 * }
 * ```
 *
 * This function returns `true` if the scope does not contain a [Job] in its
 * [context][CoroutineScope.coroutineContext].
 * This can only happen for [GlobalScope] and malformed coroutine scopes.
 *
 * For checking if the [current coroutine context][currentCoroutineContext] and not some scope's context
 * [is active][CoroutineContext.isActive], the following form can be used instead:
 *
 * ```
 * suspend fun tryDoSomething() {
 *     if (!currentCoroutineContext().isActive) return
 *     // ...
 * }
 * ```
 */
@Suppress("EXTENSION_SHADOWED_BY_MEMBER")
public val CoroutineScope.isActive: Boolean
    get() = coroutineContext[Job]?.isActive ?: true

/**
 * A [CoroutineScope] without any [Job].
 *
 * The global scope is used to launch top-level coroutines whose lifecycles are not limited by structured concurrency.
 * Since [GlobalScope] does not have a [Job], it is impossible to cancel all coroutines launched in it.
 * Likewise, there is no way to wait for all coroutines launched in it to finish.
 *
 * Active coroutines launched in `GlobalScope` do not keep the process alive.
 * They are similar to [daemon threads][https://docs.oracle.com/javase/8/docs/api/java/lang/Thread.html#setDaemon-boolean-]
 * in this regard.
 *
 * This is a **delicate** API. [GlobalScope] is easy to use to create new coroutines,
 * avoiding all bureaucracy of structured concurrency, but it also means losing all its benefits.
 * See the [CoroutineScope] documentation for a detailed explanation of structured concurrency and a list of ways
 * to obtain a [CoroutineScope] most suitable for your use case.
 *
 * ## Pitfalls
 *
 * ### Computations can happen when they have no right to or are no longer needed
 *
 * Some computations must be scoped to the lifecycle of some entity.
 * For example, after a user leaves a screen in a UI application,
 * it no longer makes sense to obtain the data needed to display that screen,
 * and attempting to update the UI may even crash the application.
 *
 * ```
 * GlobalScope.launch {
 *     val record = withContext(Dispatchers.IO) {
 *         fetchLastRecordFromServer()
 *     }
 *     withContext(Dispatchers.Main) {
 *         component.displayLastRecord(record)
 *     }
 * }
 * ```
 *
 * This code is incorrect because it does not take into account the lifecycle of the component:
 * the whole computation should be cancelled if the component is destroyed.
 *
 * If a coroutine spawned in the [GlobalScope] actually is tied to a lifecycle of some entity to function correctly,
 * the created coroutines must somehow be stored and then cancelled when the entity is destroyed.
 * The easiest way to do this is to create a [CoroutineScope] using the constructor function,
 * use it to launch the coroutines, and then cancel it when the entity is destroyed,
 * which will also lead to the coroutines being cancelled.
 *
 * ### Resource leaks
 *
 * A coroutine that never gets cancelled or resumed can be a resource leak.
 *
 * ```
 * val requests = Channel<Request>()
 * GlobalScope.launch {
 *     try {
 *         while (true) {
 *             val request = channel.receive()
 *             socket.send(request)
 *         }
 *     } finally {
 *         socket.close()
 *     }
 * }
 * ```
 *
 * If at some point, everyone stops populating the channel, the coroutine will never resume or cancel,
 * and the socket will not be closed, leading to a resource leak.
 *
 * Tying the coroutine to some lifecycle will ensure that the coroutine will get cancelled when its work
 * is no longer needed, releasing all resources it holds.
 *
 * ### Crashes
 *
 * [GlobalScope] does not have a [CoroutineExceptionHandler] installed.
 * This means that exceptions thrown in coroutines created using [launch] will be uncaught,
 * leading to platform-specific behavior, such as crashing the application (on Android and Kotlin/Native)
 * or populating the logs with potentially unnecessary information (on non-Android JVM, JS, and Wasm).
 * Please see [CoroutineExceptionHandler] for details.
 *
 * ```
 * GlobalScope.launch {
 *     // depending on your platform, this line can crash your application
 *     throw IllegalStateException()
 * }
 * ```
 *
 * One way to solve this would be to provide a [CoroutineExceptionHandler] in the [launch] arguments.
 * However, it is often much simpler to use structured concurrency
 * to ensure propagation of exceptions to the parent coroutine,
 * which usually has a way to report them: for example, [coroutineScope] or `runBlocking` will rethrow the exception
 * to the caller.
 *
 * ## How to create coroutines if not with a [GlobalScope]?
 *
 * [GlobalScope] is often used by beginners who do not see any other obvious way to create coroutines.
 * This is an antipattern and should be avoided. In this section, a brief overview of the alternatives is provided.
 *
 * In many typical usage scenarios, it is not necessary to spawn new coroutines at all to run `suspend` functions.
 * Several coroutines are needed only if the code is expected to run concurrently,
 * and when the operation execute one after another, all `suspend` functions can be called sequentially:
 *
 * ```
 * suspend fun loadConfiguration() {
 *     val config = fetchConfigFromServer() // network request
 *     updateConfiguration(config)
 * }
 * ```
 *
 * This requires that `loadConfiguration` is a `suspend` function, which is not always the case.
 * Many coroutine-aware frameworks manage coroutine scopes for you and provide a way to call `suspend` functions
 * (for example, by requiring you to provide a `suspend` lambda).
 * Try to see if the function is already called from some other `suspend` function.
 * If so, you can add the `suspend` modifier to this function and call it directly.
 *
 * If a [CoroutineScope] is necessary after all because several operations need to be run concurrently
 * in the span of a single function call,
 * the [coroutineScope] function can be used to create a new scope for the function:
 *
 * ```
 * // concurrently load configuration and data
 * suspend fun loadConfigurationAndData() {
 *     coroutineScope {
 *         launch { loadConfiguration() }
 *         launch { loadData() }
 *     }
 * }
 * ```
 *
 * A common pattern is to use [withContext] in a top-level `suspend fun main()` function:
 *
 * ```
 * suspend fun main() {
 *     // choose the dispatcher on which the coroutines should run
 *     withContext(Dispatchers.Default) {
 *         // can call `suspend` functions here!
 *     }
 * }
 * ```
 *
 * In top-level code, when launching a concurrent operation from a non-suspending context, an appropriately
 * confined instance of [CoroutineScope] shall be used instead of `GlobalScope`.
 *
 * See docs for the [CoroutineScope] interface
 * for details on structured concurrency and an extensive list of ways to obtain a [CoroutineScope].
 *
 * ### GlobalScope vs. Custom CoroutineScope
 *
 * Do not replace `GlobalScope.launch { ... }` with a `CoroutineScope().launch { ... }` constructor function call.
 * The latter suffers from all the pitfalls described above.
 * See the [CoroutineScope] documentation on the intended usage of the `CoroutineScope()` constructor function.
 *
 * ### Legitimate use cases
 *
 * There are limited circumstances under which `GlobalScope` can be legitimately and safely used,
 * such as top-level background processes that must stay active for the whole duration of the application's lifetime.
 * Because of that, any use of `GlobalScope` requires an explicit opt-in with `@OptIn(DelicateCoroutinesApi::class)`,
 * like this:
 *
 * ```
 * // A global coroutine to log statistics every second, must be always active
 * @OptIn(DelicateCoroutinesApi::class)
 * val globalScopeReporter = GlobalScope.launch(CoroutineExceptionHandler) { _, e ->
 *     logFatalError("Error in the global statistics-logging coroutine: $e")
 * }) {
 *     while (true) {
 *         delay(1.seconds)
 *         logStatistics()
 *     }
 * }
 * ```
 */
@DelicateCoroutinesApi
public object GlobalScope : CoroutineScope {
    /**
     * Returns [EmptyCoroutineContext].
     */
    override val coroutineContext: CoroutineContext
        get() = EmptyCoroutineContext
}

/**
 * Creates a [CoroutineScope] and calls the specified suspend block with this scope.
 * The provided scope inherits its [coroutineContext][CoroutineScope.coroutineContext] from the outer scope, using the
 * [Job] from that context as the parent for a new [Job].
 *
 * This function is designed for _concurrent decomposition_ of work. When any child coroutine in this scope fails,
 * this scope fails, cancelling all the other children (for a different behavior, see [supervisorScope]).
 * This function returns as soon as the given block and all its child coroutines are completed.
 * A usage of a scope looks like this:
 *
 * ```
 * suspend fun showSomeData() = coroutineScope {
 *     val data = async(Dispatchers.IO) { // <- extension on current scope
 *      ... load some UI data for the Main thread ...
 *     }
 *
 *     withContext(Dispatchers.Main) {
 *         doSomeWork()
 *         val result = data.await()
 *         display(result)
 *     }
 * }
 * ```
 *
 * The scope in this example has the following semantics:
 * 1) `showSomeData` returns as soon as the data is loaded and displayed in the UI.
 * 2) If `doSomeWork` throws an exception, then the `async` task is cancelled and `showSomeData` rethrows that exception.
 * 3) If the outer scope of `showSomeData` is cancelled, both started `async` and `withContext` blocks are cancelled.
 * 4) If the `async` block fails, `withContext` will be cancelled.
 *
 * The method may throw a [CancellationException] if the current job was cancelled externally,
 * rethrow the exception thrown by [block], or throw an unhandled [Throwable] if there is one
 * (for example, from a crashed coroutine that was started with [launch][CoroutineScope.launch] in this scope).
 */
public suspend fun <R> coroutineScope(block: suspend CoroutineScope.() -> R): R {
    contract {
        callsInPlace(block, InvocationKind.EXACTLY_ONCE)
    }
    return suspendCoroutineUninterceptedOrReturn { uCont ->
        val coroutine = ScopeCoroutine(uCont.context, uCont)
        coroutine.startUndispatchedOrReturn(coroutine, block)
    }
}

/**
 * Creates a [CoroutineScope] that wraps the given coroutine [context].
 *
 * If the given [context] does not contain a [Job] element, then a default `Job()` is created.
 * This way, failure of any child coroutine in this scope or [cancellation][CoroutineScope.cancel] of the scope itself
 * cancels all the scope's children, just like inside [coroutineScope] block.
 */
@Suppress("FunctionName")
public fun CoroutineScope(context: CoroutineContext): CoroutineScope =
    ContextScope(if (context[Job] != null) context else context + Job())

/**
 * Cancels this scope, including its job and all its children with an optional cancellation [cause].
 * A cause can be used to specify an error message or to provide other details on
 * a cancellation reason for debugging purposes.
 * Throws [IllegalStateException] if the scope does not have a job in it.
 */
public fun CoroutineScope.cancel(cause: CancellationException? = null) {
    val job = coroutineContext[Job] ?: error("Scope cannot be cancelled because it does not have a job: $this")
    job.cancel(cause)
}

/**
 * Cancels this scope, including its job and all its children with a specified diagnostic error [message].
 * A [cause] can be specified to provide additional details on a cancellation reason for debugging purposes.
 * Throws [IllegalStateException] if the scope does not have a job in it.
 */
public fun CoroutineScope.cancel(message: String, cause: Throwable? = null): Unit = cancel(CancellationException(message, cause))

/**
 * Throws the [CancellationException] that was the scope's cancellation cause if the scope is no longer [active][CoroutineScope.isActive].
 *
 * Coroutine cancellation [is cooperative](https://kotlinlang.org/docs/cancellation-and-timeouts.html#cancellation-is-cooperative)
 * and normally, it's checked if a coroutine is cancelled when it *suspends*, for example,
 * when trying to read from a [channel][kotlinx.coroutines.channels.Channel] that is empty.
 *
 * Sometimes, a coroutine does not need to perform suspending operations, but still wants to be cooperative
 * and respect cancellation.
 *
 * [ensureActive] function is inteded to be used for these scenarios and immediately bubble up the cancellation exception:
 * ```
 * val watchdogDispatcher = Dispatchers.IO.limitParallelism(1)
 * fun backgroundWork() {
 *     println("Doing bookkeeping in the background in a non-suspending manner")
 *     Thread.sleep(100L) // Sleep 100ms
 * }
 * fun postBackgroundCleanup() = println("Doing something else")
 * // Part of some non-trivial CoroutineScope-confined lifecycle
 * launch(watchdogDispatcher) {
 *     while (true) {
 *         // Repeatatively do some background work that is non-suspending
 *         backgroundWork()
 *         ensureActive() // Bail out if the scope was cancelled
 *         postBackgroundCleanup() // Won't be invoked if the scope was cancelled
 *     }
 * }
 * ```
 * This function does not do anything if there is no [Job] in the scope's [coroutineContext][CoroutineScope.coroutineContext].
 *
 * @see CoroutineScope.isActive
 * @see CoroutineContext.ensureActive
 */
public fun CoroutineScope.ensureActive(): Unit = coroutineContext.ensureActive()

/**
 * Returns the current [CoroutineContext] retrieved by using [kotlin.coroutines.coroutineContext].
 * This function is an alias to avoid name clash with [CoroutineScope.coroutineContext]:
 *
 * ```
 * // ANTIPATTERN! DO NOT WRITE SUCH A CODE
 * suspend fun CoroutineScope.suspendFunWithScope() {
 *     // Name of the CoroutineScope.coroutineContext in 'this' position, same as `this.coroutineContext`
 *     println(coroutineContext[CoroutineName])
 *     // Name of the context that invoked this suspend function, same as `kotlin.coroutines.coroutineContext`
 *     println(currentCoroutineContext()[CoroutineName])
 * }
 *
 * withContext(CoroutineName("Caller")) {
 *     // Will print 'CoroutineName("Receiver")' and 'CoroutineName("Caller")'
 *     CoroutineScope("Receiver").suspendFunWithScope()
 * }
 * ```
 *
 * This function should always be preferred over [kotlin.coroutines.coroutineContext] property even when there is no explicit clash.
 */
public suspend inline fun currentCoroutineContext(): CoroutineContext = coroutineContext
