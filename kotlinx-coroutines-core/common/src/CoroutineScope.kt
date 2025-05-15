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
 *   (typically, because the root scope of the ancestry tree is not lexically scoped).
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
 * class MyEntity : CoroutineScope by CoroutineScope(
 *     SupervisorJob() + Dispatchers.Main + CoroutineExceptionHandler { _, e ->
 *         println("Error in coroutine: $e")
 *     }
 * )
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
 * If a coroutine fails with an exception,
 * is not a coroutine created with lexically scoped coroutine builders like [coroutineScope] or [withContext],
 * *and* its parent is a normal [Job] (not a [SupervisorJob]),
 * the parent fails with that exception, too (and the same logic applies recursively to the parent of the parent, etc.):
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
 * // the calling coroutine will *not* be cancelled,
 * // even though the caller is a parent of the failed `coroutineScope`,
 * // because `coroutineScope` is a lexically scoped coroutine builder,
 * // which propagate their exceptions by rethrowing them.
 * check(currentCoroutineContext().isActive)
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
 * If several coroutines fail with non-[CancellationException] exceptions,
 * the first one to fail will be propagated, and the rest will be attached to it as
 * [suppressed exceptions][Throwable.suppressedExceptions].
 *
 * If a coroutine fails with an exception and cannot cancel its parent
 * (because its parent is a [SupervisorJob] or there is none at all),
 * the failure is reported through other channels.
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
 * **Pitfall**: this scope does not include a [CoroutineExceptionHandler] and creates a job without a parent.
 * Together, this means that if a child coroutine created with [launch] fails with an exception,
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
 *
 * @see CoroutineScope.ensureActive for a function that throws an exception instead of returning a boolean value.
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
     *
     * Note that, unlike other [CoroutineScope] implementations, this scope does not have a [Job] in its context.
     */
    override val coroutineContext: CoroutineContext
        get() = EmptyCoroutineContext
}

/**
 * Runs the given [block] in-place in a new [CoroutineScope] based on the caller coroutine context,
 * returning its result.
 *
 * The lifecycle of the new [Job] begins with starting the [block] and completes when both the [block] and
 * all the coroutines launched in the scope complete.
 *
 * The context of the new scope is obtained by combining the [currentCoroutineContext] with a new [Job]
 * whose parent is the [Job] of the caller [currentCoroutineContext] (if any).
 * The [Job] of the new scope is not a normal child of the caller coroutine but a lexically scoped one,
 * meaning that the failure of the [Job] will not affect the parent [Job].
 * Instead, the exception leading to the failure will be rethrown to the caller of this function.
 *
 * If any child coroutine in this scope fails with an exception,
 * the scope fails, cancelling all the other children and its own [block].
 * See [supervisorScope] for a similar function that allows child coroutines to fail independently.
 *
 * Together, this makes [coroutineScope] suitable for representing a task
 * that can be split into several subtasks,
 * which can be executed concurrently but have their results combined at some point,
 * all in the span of running a single function:
 *
 * ```
 * // If the current coroutine is cancelled, `firstFile`, `secondFile`,
 * // and `await()` get cancelled.
 * fun downloadAndCompareTwoFiles() = coroutineScope {
 *     val firstFile = async {
 *         // If this fails, `secondFile` and `await()` get cancelled,
 *         // and `downloadAndCompareTwoFiles` rethrows the exception,
 *         // but does not cancel the calling coroutine,
 *         // giving it a chance to recover
 *         downloadFile("1.txt")
 *     }
 *     val secondFile = async {
 *         downloadFile("2.txt")
 *     }
 *     firstFile.await().contentEquals(secondFile.await())
 * }
 * ```
 *
 * Rephrasing this in more practical terms, the specific list of structured concurrency interactions is as follows:
 * - Cancelling the caller's [currentCoroutineContext] leads to cancellation of the new [CoroutineScope]
 *   (corresponding to the code running in the [block]), which in turn cancels all the coroutines launched in it.
 * - If the new [CoroutineScope] fails with an exception
 *   (which happens if either its [block] or any child coroutine fails with an exception),
 *   the exception is rethrown to the caller,
 *   without directly affecting the caller's [Job].
 *   Note that this happens on any child coroutine's failure even if [block] finishes successfully.
 * - [coroutineScope] will only finish when all the coroutines launched in it finish.
 *   If all of them complete without failing, the [coroutineScope] returns the result of the [block] to the caller.
 *
 * There is a **prompt cancellation guarantee**: even if this function is ready to return the result, but was cancelled
 * while suspended, [CancellationException] will be thrown. See [suspendCancellableCoroutine] for low-level details.
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
 * Creates a [CoroutineScope] with the given coroutine [context].
 *
 * The provided [context] should contain a [Job], which will represent the lifecycle of the scope and become the parent
 * of any coroutines launched in this scope.
 *
 * If a [Job] is not passed, a new `Job()` is created and added to the context.
 * This is error-prone and should be avoided; it is only provided for backward compatibility.
 *
 * ## Intended usage
 *
 * ### Non-lexically-scoped [supervisorScope]
 *
 * The most common pattern of the `CoroutineScope()` builder function usage is to obtain a scope whose lifetime
 * matches the lifetime of some object, with child coroutines performing operations on that object.
 * Once the object gets destroyed, the coroutines in this scope must be cancelled.
 * This is achieved with this pattern:
 *
 * ```
 * class ThingWithItsOwnLifetime(scope: CoroutineScope? = null): AutoCloseable {
 *     private val scope = scope ?: CoroutineScope(
 *         SupervisorJob() + Dispatchers.Main +
 *         CoroutineExceptionHandler { _, e ->
 *             // handle uncaught coroutine exceptions appropriately
 *         }
 *     )
 *
 *     fun doSomethingWithThing() = scope.launch {
 *         // this computation gets cancelled when the thing gets destroyed
 *     }
 *
 *     override fun close() {
 *         // the computations should all stop running
 *         scope.cancel()
 *     }
 * }
 * ```
 *
 * The `scope` parameter is needed to support injecting coroutine scopes for testing.
 *
 * ### Non-lexically-scoped [coroutineScope]
 *
 * An equivalent to [coroutineScope] represents a group of tasks that work together to achieve one goal and should
 * succeed or fail together.
 *
 * ```
 * class SubtaskPool(scope: CoroutineScope? = null) {
 *     private val job = CompletableDeferred<Unit>()
 *     private val scope = scope ?: CoroutineScope(job + Dispatchers.IO)
 *
 *     fun addPieceOfWork() = scope.launch {
 *         // this coroutine will be cancelled when the pool is closed.
 *         // if this coroutine fails, the pool will fail too
 *     }
 *
 *     fun cancel() {
 *         // this will cancel all the coroutines launched in this scope
 *         job.cancel()
 *     }
 *
 *     suspend fun await() {
 *         job.complete(Unit)
 *         job.await()
 *     }
 * }
 * ```
 *
 * ## Pitfalls
 *
 * ### No memoization
 *
 * Every call to this function creates a new instance of [CoroutineScope].
 * If a [Job] instance is passed in the [context], it is less efficient, but is not a bug, as then,
 * the different [CoroutineScope] instances will still represent the same lifecycle and will be cancelled together.
 * However, if the [context] does not contain a [Job], then every created [CoroutineScope]
 * will be unrelated to the previous ones.
 *
 * ```
 * // // 1) ANTIPATTERN! DO NOT WRITE: creates an independent scope every time
 * // val myScope: CoroutineScope get() = CoroutineScope(Dispatchers.Main)
 * // // 2) Write this instead:
 * // val myScope: CoroutineScope       = CoroutineScope(Dispatchers.Main)
 * myScope.launch {
 *     try {
 *         awaitCancellation()
 *     } finally {
 *         println("This line will only be printed in scenario 2)")
 *     }
 * }
 * myScope.cancel()
 * ```
 *
 * ### Forgetting to propagate or handle exceptions
 *
 * Every [CoroutineScope] without an explicit [Job] in its context is a potential source of crashes or degraded
 * performance due to logging unhandled exceptions.
 * `CoroutineScope(Dispatchers.Default).launch { error("") }` is enough to crash
 * an Android or Kotlin/Native application.
 * The reason for this is that the [Job] created for this scope does not have a parent,
 * and therefore, there is no way to propagate the exception up the ancestry chain or to the caller of some function.
 *
 * One way to avoid this is to use a [CoroutineExceptionHandler] in the context of the scope:
 *
 * ```
 * val scope = CoroutineScope(
 *     Dispatchers.Default +
 *     CoroutineExceptionHandler { _, e ->
 *         // handle uncaught coroutine exceptions appropriately
 *     }
 * )
 *
 * scope.launch {
 *     error("This is okay") // this will not crash the application
 * }
 * ```
 *
 * Another way is to provide a [Job] that knows how to propagate the exception.
 * See [CoroutineExceptionHandler] for details of how exceptions are propagated.
 * Here is an example of using a [CompletableDeferred] in the scope's [context] to properly handle exceptions:
 *
 * ```
 * val myDeferred = CompletableDeferred<Unit>()
 * try {
 *     val scope = CoroutineScope(myDeferred + Dispatchers.Default)
 *     scope.launch {
 *         error("This is okay") // this will not crash the application
 *     }
 * } finally {
 *     // Do not forget to complete and await the deferred to check for exceptions!
 *     myDeferred.complete(Unit)
 *     // The exceptions from child coroutines will be thrown here:
 *     myDeferred.await()
 * }
 * ```
 *
 * This specific example is not recommended, as it is easier to use [coroutineScope] to achieve a similar effect.
 * However, it is more flexible, as it allows invoking the `finally` block separately.
 *
 * ### Surprising interactions between failing children
 *
 * If a [Job] is not passed in the context of this function explicitly,
 * one is created using the `Job()` constructor function.
 * As opposed to a [SupervisorJob], this [Job] will fail if any of its children fail.
 *
 * ```
 * val scope = CoroutineScope(Dispatchers.Main + CoroutineExceptionHandler { _, e ->
 *    println("Coroutine failed with exception $e")
 * })
 * scope.launch {
 *     updateUI("Operation started!")
 *     // this coroutine will be cancelled
 *     // when the other coroutine fails
 *     delay(2.seconds)
 *     // this line will not be executed
 *     updateUI("Operation finished!")
 * }
 * scope.launch {
 *     error("This will cancel the other coroutines")
 * }
 * ```
 *
 * This behavior is suitable for cases where one task is decomposed into several subtasks,
 * and one failure means the whole operation can no longer succeed and will have to be cancelled.
 * However, in the far more common scenarios where `CoroutineScope()` represents the lifecycle of some entity
 * that supports multiple independent concurrent operations,
 * this is not the desired behavior.
 *
 * Explicitly using a [SupervisorJob] in the context of the scope is the recommended way to avoid this.
 *
 * ### Unintentionally passing a [Job] in the context
 *
 * Sometimes, a [Job] is passed in the context of this function unintentionally,
 * leading to unpredictable interactions between several scopes.
 *
 * Examples of this include `CoroutineScope(currentCoroutineContext())`, `CoroutineScope(coroutineContext)`,
 * `CoroutineScope(scope.coroutineContext)`, or any variations thereof that add new elements or remove existing ones.
 *
 * In all of these cases, the [Job] in the context of the new scope will be used as the parent job of all the
 * coroutines in the newly created scope, meaning this scope will essentially be a view of some other scope,
 * similar to what the [CoroutineScope.plus] operation produces.
 *
 * ```
 * // ANTIPATTERN! DO NOT WRITE SUCH CODE
 * suspend fun foo() {
 *     val scope = CoroutineScope(currentCoroutineContext())
 *     scope.launch {
 *         delay(1.seconds)
 *         println("foo()'s child coroutine finished")
 *     }
 * }
 *
 * suspend fun bar() {
 *     coroutineScope {
 *         foo()
 *         println("foo() finished, but the new coroutine is still running")
 *     }
 * }
 * ```
 *
 * In this example, the new coroutine will be launched in the scope *of the caller*,
 * and `foo()` will not await the completion of this coroutine.
 * To await the completion, use [coroutineScope] instead:
 *
 * ```
 * suspend fun foo() = coroutineScope {
 *     launch {
 *         delay(1.seconds)
 *         println("foo()'s child coroutine finished")
 *     }
 * } // `foo()` will only return when the child coroutine completes
 *
 * suspend fun bar() {
 *     coroutineScope {
 *         foo()
 *         println("foo() finished, along with its child coroutine")
 *     }
 * }
 * ```
 *
 * If launching a coroutine in the context of the caller is the desired behavior,
 * make it explicit by passing the context:
 *
 * ```
 * fun foo(scope: CoroutineScope) {
 *     scope.launch {
 *         delay(1.seconds)
 *         println("foo()'s child coroutine finished")
 *     }
 * }
 *
 * suspend fun bar() {
 *     coroutineScope {
 *         foo(this)
 *         println("foo() created a child coroutine in `this` scope")
 *     }
 * }
 * ```
 */
@Suppress("FunctionName")
public fun CoroutineScope(context: CoroutineContext): CoroutineScope =
    ContextScope(if (context[Job] != null) context else context + Job())

/**
 * Cancels this scope, including its job and all its children with an optional cancellation [cause].
 *
 * A cause can be used to specify an error message or to provide other details on
 * a cancellation reason for debugging purposes.
 *
 * Throws [IllegalStateException] if the scope does not have a job in it.
 *
 * This function is shorthand for `coroutineContext[Job]?.cancel(cause) ?: throw IllegalStateException()`.
 *
 * ## Usage
 *
 * ### Cancelling non-lexically scoped coroutines
 *
 * The primary purpose of this function is to cancel a manually created [CoroutineScope] when its lifecycle ends.
 *
 * ```
 * class ThingWithItsOwnLifetime(scope: CoroutineScope? = null): AutoCloseable {
 *     private val scope = scope ?: CoroutineScope(
 *         SupervisorJob() + Dispatchers.Main +
 *         CoroutineExceptionHandler { _, e ->
 *             // handle uncaught coroutine exceptions appropriately
 *         }
 *     )
 *
 *     override fun close() {
 *         // the computations should all stop running
 *         scope.cancel()
 *     }
 * ```
 *
 * Failing to cancel the scope when it is no longer needed will lead to resource leaks
 * and can also potentially crash the program if some object used by the child coroutines becomes destroyed.
 *
 * ### Cancelling lexical [CoroutineScope]
 *
 * For lexically scoped coroutines, such as those created with [coroutineScope] or [withContext],
 * canceling the scope explicitly is very rarely required.
 *
 * If no child coroutines were started, but it became obvious that the computation won't be needed,
 * the scope can simply be exited:
 *
 * ```
 * coroutineScope {
 *     if (computationNotNeeded) return@coroutineScope
 *     // Start some child coroutines
 *     // ...
 * }
 * ```
 *
 * Also, if the caller is cancelled, the scope will be cancelled as well, so there is no need to cancel it explicitly.
 *
 * [cancel] may be useful in cases when one child coroutine detects that the whole parent scope is no longer needed
 * and wants to cancel it:
 *
 * ```
 * coroutineScope {
 *     val parentScope = this
 *     launch {
 *         val userRequest = getUserRequest()
 *         if (userRequest == TERMINATE) {
 *             parentScope.cancel()
 *         }
 *         // Do something with the request
 *         // ...
 *     }
 *     // Start other child coroutines...
 * }
 * ```
 *
 * ## Pitfalls
 *
 * ### Cancelling oneself
 *
 * Cancelling a scope does not mean the computation finishes immediately,
 * as coroutine cancellation [is cooperative](https://kotlinlang.org/docs/cancellation-and-timeouts.html#cancellation-is-cooperative).
 * Only the next suspension point will observe the cancellation.
 * For example:
 *
 * ```
 * try {
 *     coroutineScope {
 *         cancel()
 *         println("Will be printed anyway!")
 *     }
 * } catch (e: CancellationException) {
 *     println(
 *         "The scope was cancelled " +
 *         "(the parent coroutine is still active: ${currentCoroutineContext().isActive})"
 *     )
 *     throw e
 * }
 * ```
 *
 * will output
 *
 * ```
 * Will be printed anyway!
 * The scope was cancelled (the parent coroutine is still active: true)
 * ```
 *
 * Use `return` to immediately return from the scope after cancelling it:
 *
 * ```
 * coroutineScope {
 *     cancel()
 *     return@coroutineScope
 *     println("Will not be printed")
 * }
 * ```
 */
public fun CoroutineScope.cancel(cause: CancellationException? = null) {
    val job = coroutineContext[Job] ?: error("Scope cannot be cancelled because it does not have a job: $this")
    job.cancel(cause)
}

/**
 * Cancels this scope with a [CancellationException] with the given [message] and [cause].
 *
 * Shorthand for `cancel(CancellationException(message, cause))`.
 */
public fun CoroutineScope.cancel(message: String, cause: Throwable? = null): Unit = cancel(CancellationException(message, cause))

/**
 * Throws the [CancellationException] that was the scope's cancellation cause
 * if the scope is no longer [active][CoroutineScope.isActive].
 *
 * Coroutine cancellation [is cooperative](https://kotlinlang.org/docs/cancellation-and-timeouts.html#cancellation-is-cooperative),
 * and normally, it's checked if a coroutine is cancelled when it *suspends*, for example,
 * when trying to read from a [channel][kotlinx.coroutines.channels.Channel] that is empty.
 *
 * Sometimes, a coroutine does not need to perform suspending operations but still wants to be cooperative
 * and respect cancellation.
 *
 * [ensureActive] function is intended to be used for these scenarios and immediately bubble up the cancellation exception:
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
 *         // Repeatedly do some background work that is non-suspending
 *         backgroundWork()
 *         ensureActive() // Bail out if the scope was cancelled
 *         postBackgroundCleanup() // Won't be invoked if the scope was cancelled
 *     }
 * }
 * ```
 * This function does not do anything if there is no [Job] in the scope's [coroutineContext][CoroutineScope.coroutineContext].
 *
 * For ensuring that the [current coroutine context][currentCoroutineContext] and not some scope's context
 * [is active][CoroutineContext.isActive], the following form can be used instead:
 *
 * ```
 * suspend fun doSomething() {
 *     // throw if we are not allowed to suspend
 *     currentCoroutineContext().ensureActive()
 *     // ...
 * }
 * ```
 *
 * @see CoroutineScope.isActive for a version that returns a boolean value instead of throwing an exception.
 */
public fun CoroutineScope.ensureActive(): Unit = coroutineContext.ensureActive()

/**
 * Returns the current [CoroutineContext] retrieved by using [kotlin.coroutines.coroutineContext].
 *
 * This function is an alias to avoid name clash with [CoroutineScope.coroutineContext]:
 *
 * ```
 * // ANTIPATTERN! DO NOT WRITE SUCH CODE
 * suspend fun CoroutineScope.suspendFunWithScope() {
 *     // Name of the CoroutineScope.coroutineContext in 'this' position, same as `this.coroutineContext`
 *     println(coroutineContext[CoroutineName])
 *     // Name of the context that invoked this suspend function, same as `kotlin.coroutines.coroutineContext`
 *     println(currentCoroutineContext()[CoroutineName])
 * }
 *
 * withContext(CoroutineName("Caller")) {
 *     // Will print 'CoroutineName("Receiver")' and 'CoroutineName("Caller")'
 *     CoroutineScope(CoroutineName("Receiver")).suspendFunWithScope()
 * }
 * ```
 *
 * This function should always be preferred over [kotlin.coroutines.coroutineContext] property
 * even when there is no explicit clash.
 *
 * Usage example:
 *
 * ```
 * // log an event while specifying the current coroutine
 * println("[${currentCoroutineContext()[Job]}] Hello, World!")
 * ```
 *
 * Consider using [coroutineScope] instead of this function to obtain not only the current context
 * but also a new [CoroutineScope] that allows easily launching coroutines and waiting for their completion.
 */
public suspend inline fun currentCoroutineContext(): CoroutineContext = coroutineContext
