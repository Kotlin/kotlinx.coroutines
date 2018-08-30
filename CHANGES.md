# Change log for kotlinx.coroutines

## Version 0.25.0

* Major rework on exception-handling and cancellation in coroutines (see #333, #452 and #451):
  * New ["Exception Handling" section in the guide](coroutines-guide.md#exception-handling) explains exceptions in coroutines. 
  * Semantics of `Job.cancel` resulting `Boolean` value changed &mdash; `true` means exception was handled by the job, caller shall handle otherwise.
  * Exceptions are properly propagated from children to parents.
  * Installed `CoroutineExceptionHandler` for a family of coroutines receives one aggregated exception in case of failure.
  * Change `handleCoroutineException` contract, so custom exception handlers can't break coroutines machinery. 
  * Unwrap `JobCancellationException` properly to provide exception transparency over whole call chain.
* Introduced support for thread-local elements in coroutines context (see #119):
  * `ThreadContextElement` API for custom thread-context sensitive context elements.
  * `ThreadLocal.asContextElement()` extension function to convert an arbitrary thread-local into coroutine context element.
  * New ["Thread-local data" subsection in the guide](coroutines-guide.md#thread-local-data) with examples.
  * SLF4J Mapped Diagnostic Context (MDC) integration is provided via `MDCContext` element defined in [`kotlinx-coroutines-slf4j`](integration/kotlinx-coroutines-slf4j/README.md) integration module.
* Introduced IO dispatcher to offload blocking I/O-intensive tasks (see #79).
* Introduced `ExecutorCoroutineDispatcher` instead of `CloseableCoroutineDispatcher` (see #385). 
* Built with Kotlin 1.2.61 and Kotlin/Native 0.8.2.
* JAR files for `kotlinx-coroutines` are now [JEP 238](http://openjdk.java.net/jeps/238) multi-release JAR files.
  * On JDK9+ `VarHandle` is used for atomic operations instead of `Atomic*FieldUpdater` for better performance.
  * See [AtomicFu](https://github.com/Kotlin/kotlinx.atomicfu/blob/master/README.md) project for details.
* Reversed addition of `BlockingChecker` extension point to control where `runBlocking` can be used (see #227).
  * `runBlocking` can be used anywhere without limitations (again), but it would still cause problems if improperly used on UI thread.
* Corrected return-type of `EventLoop` pseudo-constructor (see #477, PR by @Groostav).  
* Fixed `as*Future()` integration functions to catch all `Throwable` exceptions (see #469).
* Fixed `runBlocking` cancellation (see #501).
* Fixed races and timing bugs in `withTimeoutOrNull` (see #498).
* Execute `EventLoop.invokeOnTimeout` in `DefaultDispatcher` to allow busy-wait loops inside `runBlocking` (see #479).
* Removed `kotlinx-coroutines-io` module from the project, it has moved to [kotlinx-io](https://github.com/kotlin/kotlinx-io/).
* Provide experimental API to create limited view of experimental dispatcher (see #475). 
* Various minor fixes by @LouisCAD, @Dmitry-Borodin.

## Version 0.24.0

* Fully multiplatform release with Kotlin/Native support (see #246):
  * Only single-threaded operation inside `runBlocking` event loop is supported at this moment.
  * See details on setting up build environment [here](native/README.md). 
* Improved channels:
  * Introduced `SendChannel.invokeOnClose` (see #341).
  * Make `close`, `cancel`, `isClosedForSend`, `isClosedForReceive` and `offer` linearizable with other operations (see #359).
  * Fixed bug when send operation can be stuck in channel forever.
  * Fixed broadcast channels on JS (see #412).
* Provides `BlockingChecker` mechanism which checks current context (see #227).
  * Attempts to use `runBlocking` from any supported UI thread (Android, JavaFx, Swing) will result in exception.
* Android: 
  * Worked around Android bugs with zero-size ForkJoinPool initialization (see #432, #288).
  * Introduced `UI.immediate` extension as performance-optimization to immediately execute tasks which are invoked from the UI thread  (see #381). 
    * Use it only when absolutely needed. It breaks asynchrony of coroutines and may lead to surprising and unexpected results.
* Fixed materialization of a `cause` exception for `Job` onCancelling handlers (see #436).  
* Fixed JavaFx `UI` on Java 9 (see #443).
* Fixed and documented the order between cancellation handlers and continuation resume (see #415).
* Fixed resumption of cancelled continuation (see #450).
* Includes multiple fixes to documentation contributed by @paolop, @SahilLone, @rocketraman, @bdavisx, @mtopolnik, @Groostav.   
* Experimental coroutines scheduler preview (JVM only):
  * Written from scratch and optimized for communicating coroutines.
  * Performs significantly better than ForkJoinPool on coroutine benchmarks and for connected applications with [ktor](http://ktor.io).
  * Supports automatic creating of new threads for blocking operations running on the same thread pool (with an eye on solving #79), but there is no stable public API for it just yet.
  * For preview, run JVM with `-Dkotlinx.coroutines.scheduler` option. In this case `DefaultDispatcher` is set to new experimental scheduler instead of FJP-based `CommonPool`.
  * Submit your feedback to issue #261.

## Version 0.23.4

* Recompiled with Kotlin 1.2.51 to solve broken metadata problem (see [KT-24944](https://youtrack.jetbrains.com/issue/KT-24944)).

## Version 0.23.3

* Kotlin 1.2.50.
* JS: Moved to atomicfu version 0.10.3 that properly matches NPM & Kotlin/JS module names (see #396).
* Improve source-code compatibility with previous (0.22.x) version of `openChannel().use { ... }` pattern by providing deprecated extension function `use` on `ReceiveChannel`.

## Version 0.23.2

* IO: fix joining and continuous writing byte array interference.

## Version 0.23.1

* JS: Fix dependencies in NPM: add "kotlinx-atomicfu" dependency (see #370).
* Introduce `broadcast` coroutine builder (see #280):
  * Support `BroadcastChannel.cancel` method to drop the buffer.
  * Introduce `ReceiveChannel.broadcast()` extension. 
* Fixed a bunch of doc typos (PRs by @paolop).
* Corrected previous version's release notes (PR by @ansman).  

## Version 0.23.0

* Kotlin 1.2.41
* **Coroutines core module is made mostly cross-platform for JVM and JS**:
  * Migrate channels and related operators to common, so channels can be used from JS (see #201).
  * Most of the code is shared between JVM and JS versions using cross-platform version of [AtomicFU](https://github.com/Kotlin/kotlinx.atomicfu) library.
  * The recent version of Kotlin allows default parameters in common code (see #348).
  * The project is built using Gradle 4.6. 
* **Breaking change**: `CancellableContinuation` is not a `Job` anymore (see #219):
  * It does not affect casual users of `suspendCancellableCoroutine`, since all the typically used functions are still there.
  * `CancellableContinuation.invokeOnCompletion` is deprecated now and its semantics had subtly changed:
     * `invokeOnCancellation` is a replacement for `invokeOnCompletion` to install a handler.
     * The handler is **not** invoked on `resume` which corresponds to the typical usage pattern.
     * There is no need to check for `cont.isCancelled` in a typical handler code anymore (since handler is invoked only when continuation is cancelled). 
     * Multiple cancellation handlers cannot be installed.
     * Cancellation handlers cannot be removed (disposed of) anymore.  
  * This change is designed to allow better performance of suspending cancellable functions: 
     * Now `CancellableContinuation` implementation has simpler state machine and is implemented more efficiently. 
  * Exception handling in `AbstractContinuation` (that implements `CancellableContinuation`) is now consistent: 
     * Always prefer exception thrown from coroutine as exceptional reason, add cancellation cause as suppressed exception.      
* **Big change**: Deprecate `CoroutineScope.coroutineContext`:
  * It is replaced with top-level `coroutineContext` function from Kotlin standard library.
* Improve `ReceiveChannel` operators implementations to guarantee closing of the source channels under all circumstances (see #279):
  * `onCompletion` parameter added to `produce` and all other coroutine builders.
  * Introduce `ReceiveChannel.consumes(): CompletionHandler` extension function.
* Replace `SubscriptionReceiveChannel` with `ReceiveChannel` (see #283, PR by @deva666).
  * `ReceiveChannel.use` extension is introduced to preserve source compatibility, but is deprecated.
    * `consume` or `consumeEach` extensions should be used for channels.
    * When writing operators, `produce(onCompletion=consumes())  { ... }` pattern shall be used (see #279 above). 
* JS: Kotlin is declared as peer dependency (see #339, #340, PR by @ansman).  
* Invoke exception handler for actor on cancellation even when channel was successfully closed, so exceptions thrown by actor are always reported (see #368).
* Introduce `awaitAll` and `joinAll` for `Deferred` and `Job` lists correspondingly (see #171).  
* Unwrap `CompletionException` exception in `CompletionStage.await` slow-path to provide consistent results (see #375).
* Add extension to `ExecutorService` to return `CloseableCoroutineDispatcher` (see #278, PR by @deva666).
* Fail with proper message during build if JDK_16 is not set (see #291, PR by @venkatperi).
* Allow negative timeouts in `delay`, `withTimeout` and `onTimeout` (see #310).
* Fix a few bugs (leaks on cancellation) in `delay`:
  * Invoke `clearTimeout` on cancellation in JSDispatcher.
  * Remove delayed task on cancellation from internal data structure on JVM.
* Introduce `ticker` function to create "ticker channels" (see #327):
  * It provides analogue of RX `Observable.timer` for coroutine channels.
  * It is currently supported on JVM only.
* Add a test-helper class `TestCoroutineContext` (see #297, PR by @streetsofboston).  
  * It is currently supported on JVM only.
  * Ticker channels (#327) are not yet compatible with it. 
* Implement a better way to set `CoroutineContext.DEBUG` value (see #316, PR by @dmytrodanylyk):
  * Made `CoroutineContext.DEBUG_PROPERTY_NAME` constant public.
  * Introduce public constants with `"on"`, `"off"`, `"auto"` values.
* Introduce system property to control `CommonPool` parallelism (see #343):
  * `CommonPool.DEFAULT_PARALLELISM_PROPERTY_NAME` constant is introduced with a value of "kotlinx.coroutines.default.parallelism".
* Include package-list files into documentation site (see #290).
* Fix various typos in docs (PRs by @paolop and @ArtsiomCh).  

## Version 0.22.5

* JS: Fixed main file reference in [NPM package](https://www.npmjs.com/package/kotlinx-coroutines-core)
* Added context argument to `Channel.filterNot` (PR by @jcornaz).
* Implemented debug `toString` for channels (see #185).

## Version 0.22.4

* JS: Publish to NPM (see #229).
* JS: Use node-style dispatcher on ReactNative (see #236).
* [jdk8 integration](integration/kotlinx-coroutines-jdk8/README.md) improvements: 
  * Added conversion from `CompletionStage` to `Deferred` (see #262, PR by @jcornaz).
  * Use fast path in `CompletionStage.await` and make it cancellable.

## Version 0.22.3

* Fixed `produce` builder to close the channel on completion instead of cancelling it, which lead to lost elements with buffered channels (see #256).
* Don't use `ForkJoinPool` if there is a `SecurityManager` present to work around JNLP problems (see #216, PR by @NikolayMetchev). 
* JS: Check for undefined `window.addEventListener` when choosing default coroutine dispatcher (see #230, PR by @ScottPierce).
* Update 3rd party dependencies:
  * [kotlinx-coroutines-rx1](reactive/kotlinx-coroutines-rx1) to RxJava version `1.3.6`.
  * [kotlinx-coroutines-rx2](reactive/kotlinx-coroutines-rx2) to RxJava version `2.1.9`.
  * [kotlinx-coroutines-guava](integration/kotlinx-coroutines-guava) to Guava version `24.0-jre`.
  
## Version 0.22.2

* Android: Use @Keep annotation on AndroidExceptionPreHandler to fix the problem on Android with minification enabled (see #214).
* Reactive: Added `awaitFirstOrDefault` and `awaitFirstOrNull` extensions (see #224, PR by @konrad-kaminski).
* Core: Fixed `withTimeout` and `withTimeoutOrNull` that should not use equals on result (see #212, PR by @konrad-kaminski).
* Core: Fixed hanged receive from a closed subscription of BroadcastChannel (see #226).
* IO: fixed error propagation (see https://github.com/ktorio/ktor/issues/301).
* Include common sources into sources jar file to work around KT-20971.
* Fixed bugs in documentation due to MPP.

## Version 0.22.1

* Migrated to Kotlin 1.2.21.
* Improved `actor` builder documentation (see #210) and fixed bugs in rendered documentation due to multiplatform.
* Fixed `runBlocking` to properly support specified dispatchers (see #209).
* Fixed data race in `Job` implementation (it was hanging at `LockFreeLinkedList.helpDelete` on certain stress tests).
* `AbstractCoroutine.onCancellation` is invoked before cancellation handler that is set via `invokeOnCompletion`.
* Ensure that `launch` handles uncaught exception before another coroutine that uses `join` on it resumes (see #208).

## Version 0.22

* Migrated to Kotlin 1.2.20.
* Introduced stable public API for `AbstractCoroutine`:
  * Implements `Job`, `Continuation`, and `CoroutineScope`.
  * Has overridable `onStart`, `onCancellation`, `onCompleted` and `onCompletedExceptionally` functions.
  * Reactive integration modules are now implemented using public API only.
  * Notifies onXXX before all the installed handlers, so `launch` handles uncaught exceptions before "joining" coroutines wakeup (see #208).

## Version 0.21.2

* Fixed `openSubscription` extension for reactive `Publisher`/`Observable`/`Flowable` when used with `select { ... }` and added an optional `request` parameter to specify how many elements are requested from publisher in advance on subscription (see #197).
* Simplified implementation of `Channel.flatMap` using `toChannel` function to work around Android 5.0 APK install SIGSEGV (see #205).

## Version 0.21.1

* Improved performance of coroutine dispatching (`DispatchTask` instance is no longer allocated).
* Fixed `Job.cancel` and `CompletableDeferred.complete` to support cancelling/completing states and properly wait for their children to complete on join/await (see #199).
* Fixed a bug in binary heap implementation (used internally by `delay`) which could have resulted in wrong delay time in rare circumstances.
* Coroutines library for [Kotlin/JS](js/README.md):
  * `Promise.asDeferred` immediately installs handlers to avoid "Unhandled promise rejection" warning.
  * Use `window.postMessage` instead of `setTimeout` for coroutines inside the browser to avoid timeout throttling (see #194).
  * Use custom queue in `Window.awaitAnimationFrame` to align all animations and reduce overhead.
  * Introduced `Window.asCoroutineDispatcher()` extension function.

## Version 0.21

* Migrated to Kotlin 1.2.10.
* Coroutines library for [Kotlin/JS](js/README.md) and [multiplatform projects](https://kotlinlang.org/docs/reference/multiplatform.html) (see #33):
  * `launch` and `async` coroutine builders.
  * `Job` and `Deferred` light-weight future with cancellation support.
  * `delay` and `yield` top-level suspending functions.
  * `await` extension for JS `Promise` and `asPromise`/`asDeferred` conversions.
  * `promise` coroutine builder.
  * `Job()` and `CompletableDeferred()` factories.
  * Full support for parent-child coroutine hierarchies.
  * `Window.awaitAnimationFrame` extension function.
  * [Sample frontend Kotlin/JS application](js/example-frontend-js/README.md) with coroutine-driven animations.
* `run` is deprecated and renamed to `withContext` (see #134).
* `runBlocking` and `EventLoop` implementations optimized (see #190).

## Version 0.20

* Migrated to Kotlin 1.2.0.
* Channels:
  * Sequence-like `filter`, `map`, etc extensions on `ReceiveChannel` are introduced (see #88 by @fvasco and #69 by @konrad-kaminski).
  * Introduced `ReceiveChannel.cancel` method.
  * All operators on `ReceiveChannel` fully consume the original channel (`cancel` it when they are done) using a helper `consume` extension.
  * Deprecated `ActorJob` and `ProducerJob`; `actor` now returns `SendChannel` and `produce` returns `ReceiveChannel` (see #127).
  * `SendChannel.sendBlocking` extension method (see #157 by @@fvasco).
* Parent-child relations between coroutines:
  * Introduced an optional `parent` job parameter for all coroutine builders so that code with an explict parent `Job` is more natural.
  * Added `parent` parameter to `CompletableDeferred` constructor.
  * Introduced `Job.children` property.
  * `Job.cancelChildren` is now an extension (member is deprecated and hidden).
  * `Job.joinChildren` extension is introduced.
  * Deprecated `Job.attachChild` as a error-prone API.
  * Fixed StackOverflow when waiting for a lot of completed children that did not remove their handlers from the parent.
* Use `java.util.ServiceLoader` to find default instances of `CoroutineExceptionHandler`.
* Android UI integration:
  * Use `Thread.getUncaughtExceptionPreHandler` to make sure that exceptions are logged before crash (see #148).
  * Introduce `UI.awaitFrame` for animation; added sample coroutine-based animation application for Android [here](ui/kotlinx-coroutines-android/animation-app).
  * Fixed `delay(Long.MAX_VALUE)` (see #161)  
* Added missing `DefaultDispatcher` on some reactive operators (see #174 by @fvasco)
* Fixed `actor` and `produce` so that a cancellation of a Job cancels the underlying channel (closes and removes all the pending messages).  
* Fixed sporadic failure of `example-context-06` (see #160)
* Fixed hang of `Job.start` on lazy coroutine with attached `invokeOnCompletion` handler.
* A more gradual introduction to `runBlocking` and coroutines in the [guide](coroutines-guide.md) (see #166).

## Version 0.19.3

* Fixed `send`/`openSubscription` race in `ArrayBroadcastChannel`.
  This race lead to stalled (hanged) `send`/`receive` invocations.
* Project build has been migrated to Gradle.  

## Version 0.19.2

* Fixed `ArrayBroadcastChannel` receive of stale elements on `openSubscription`. 
  Only elements that are sent after invocation of `openSubscription` are received now.
* Added a default value for `context` parameter to `rxFlowable` (see #146 by @PhilGlass).
* Exception propagation logic from cancelled coroutines is adjusted (see #152):
  * When cancelled coroutine crashes due to some other exception, this other exception becomes the cancellation reason 
    of the coroutine, while the original cancellation reason is suppressed.
  * `UnexpectedCoroutineException` is no longer used to report those cases as is removed.
  * This fixes a race between crash of CPU-consuming coroutine and cancellation which resulted in an unhandled exception 
    and lead to crashes on Android.
* `run` uses cancelling state & propagates exceptions when cancelled (see #147):
  * When coroutine that was switched into a different dispatcher using `run` is cancelled, the run invocation does not 
    complete immediately, but waits until the body completes.
  * If the body completes with exception, then this exception is propagated.
* No `Job` in `newSingleThreadContext` and `newFixedThreadPoolContext` anymore (see #149, #151):
  * This resolves the common issue of using `run(ctx)` where ctx comes from either `newSingleThreadContext` or 
    `newFixedThreadPoolContext` invocation. They both used to return a combination of dispatcher + job,
     and this job was overriding the parent job, thus preventing propagation of cancellation. Not anymore.
  * `ThreadPoolDispatcher` class is now public and is the result type for both functions. 
     It has the `close` method to release the thread pool.

## Version 0.19.1

* Failed parent Job cancels all children jobs, then waits for them them.
  This makes parent-child hierarchies easier to get working right without
  having to use `try/catch` or other exception handlers.  
* Fixed a race in `ArrayBroadcastChannel` between `send` and `openChannel` invocations
  (see #138).   
* Fixed quite a rare race in `runBlocking` that resulted in `AssertionError`. 
  Unfortunately, cannot write a reliable stress-test to reproduce it. 
* Updated Reactor support to leverage Bismuth release train 
  (contributed by @sdeleuze, see PR #141)

## Version 0.19

* This release is published to Maven Central.
* `DefaultDispatcher` is introduced (see #136):
  * `launch`, `async`, `produce`, `actor` and other integration-specific coroutine builders now use 
    `DefaultDispatcher` as the default value for their `context` parameter.
  * When a context is explicitly specified, `newCoroutineContext` function checks if there is any
    interceptor/dispatcher defined in the context and uses `DefaultDispatcher` if there is none.  
  * `DefaultDispatcher` is currently defined to be equal to `CommonPool`.     
  * Examples in the [guide](coroutines-guide.md) now start with `launch { ... }` code and explanation on the nature
    and the need for coroutine context starts in "Coroutine context and dispatchers" section.  
* Parent coroutines now wait for their children (see #125):
  * Job _completing_ state is introduced in documentation as a state in which parent coroutine waits for its children.
  * `Job.attachChild` and `Job.cancelChildren` are introduced.
  * `Job.join` now always checks cancellation status of invoker coroutine for predictable behavior when joining
     failed child coroutine. 
  * `Job.cancelAndJoin` extension is introduced.    
  * `CoroutineContext.cancel` and `CoroutineContext.cancelChildren` extensions are introduced for convenience. 
  * `withTimeout`/`withTimeoutOrNull` blocks become proper coroutines that have `CoroutineScope` and wait for children, too.
  * Diagnostics in cancellation and unexpected exception messages are improved, 
    coroutine name is included in debug mode.
  * Fixed cancellable suspending functions to throw `CancellationException` (as was documented before) even when 
    the coroutine is cancelled with another application-specific exception.
  * `JobCancellationException` is introduced as a specific subclass of `CancellationException` which is 
    used for coroutines that are cancelled without cause and to wrap application-specific exceptions.   
  * `Job.getCompletionException` is renamed to `Job.getCancellationException` and return a wrapper exception if needed.
  * Introduced `Deferred.getCompletionExceptionOrNull` to get not-wrapped exception result of `async` task.
  * Updated docs for `Job` & `Deferred` to explain parent/child relations.
* `select` expression is modularized:
  * `SelectClause(0,1,2)` interfaces are introduced, so that synchronization
    constructs can define their select clauses without having to modify
    the source of the `SelectBuilder` in `kotlinx-corounes-core` module.
  * `Job.onJoin`, `Deferred.onAwait`, `Mutex.onLock`, `SendChannel.onSend`, `ReceiveChannel.onReceive`, etc
    that were functions before are now properties returning the corresponding select clauses. Old functions
    are left in bytecode for backwards compatibility on use-site, but any outside code that was implementing those 
    interfaces by itself must be updated.  
  * This opens road to moving channels into a separate module in future updates.
* Renamed `TimeoutException` to `TimeoutCancellationException` (old name is deprecated).  
* Fixed various minor problems:    
  * JavaFx toolkit is now initialized by `JavaFx` context (see #108).
  * Fixed lost ACC_STATIC on <clinit> methods (see #116).
  * Fixed link to source code from documentation (see #129).
  * Fixed `delay` in arbitrary contexts (see #133).
* `kotlinx-coroutines-io` module is introduced. It is a work-in-progress on `ByteReadChannel` and `ByteWriteChannel`
   interfaces, their implementations, and related classes to enable convenient coroutine integration with various 
   asynchronous I/O libraries and sockets. It is currently _unstable_ and **will change** in the next release.  

## Version 0.18

* Kotlin 1.1.4 is required to use this version, which enables:
  * `withLock` and `consumeEach` functions are now inline suspend functions.
  * `JobSupport` class implementation is optimized (one fewer field).
* `TimeoutException` is public (see #89).
* Improvements to `Mutex` (courtesy of @fvasco):
  * Introduced `holdsLock` (see #92).
  * Improved documentation on `Mutex` fairness (see #90).
* Fixed NPE when `ArrayBroadcastChannel` is closed concurrently with receive (see #97).
* Fixed bug in internal class LockFreeLinkedList that resulted in ISE under stress in extremely rare circumstances.
* Integrations:
  * [quasar](integration/kotlinx-coroutines-quasar): Introduced integration with suspendable JVM functions
    that are instrumented with [Parallel Universe Quasar](http://docs.paralleluniverse.co/quasar/) 
    (thanks to the help of @pron). 
  * [reactor](reactive/kotlinx-coroutines-reactor): Replaced deprecated `setCancellation` with `onDipose` and 
    updated to Aluminium-SR3 release (courtesy of @yxf07, see #96) 
  * [jdk8](integration/kotlinx-coroutines-jdk8): Added adapters for `java.time` classes (courtesy of @fvasco, see #93)     

## Version 0.17

* `CompletableDeferred` is introduced as a set-once event-like communication primitive (see #70).
  * [Coroutines guide](coroutines-guide.md) uses it in a section on actors.
  * `CompletableDeferred` is an interface with private impl (courtesy of @fvasco, see #86).
  * It extends `Deferred` interface with `complete` and `completeExceptionally` functions.
* `Job.join` and `Deferred.await` wait until a cancelled coroutine stops execution (see #64). 
  * `Job` and `Deferred` have a new _cancelling_ state which they enter on invocation of `cancel`.
  * `Job.invokeOnCompletion` has an additional overload with `onCancelling: Boolean` parameter to 
    install handlers that are fired as soon as coroutine enters _cancelling_ state as opposed
    to waiting until it _completes_.
  * Internal `select` implementation is refactored to decouple it from `JobSupport` internal class 
    and to optimize its state-machine.  
  * Internal `AbstractCoroutine` class is refactored so that it is extended only by true coroutines, 
    all of which support the new _cancelling_ state.  
* `CoroutineScope.context` is renamed to `coroutineContext` to avoid conflicts with other usages of `context`
  in applications (like Android context, see #75).       
* `BroadcastChannel.open` is renamed to `openSubscription` (see #54).
* Fixed `StackOverflowError` in a convoy of `Mutex.unlock` invokers with `Unconfined` dispatcher (see #80).
* Fixed `SecurityException` when trying to use coroutines library with installed `SecurityManager`.
* Fixed a bug in `withTimeoutOrNull` in case with nested timeouts when coroutine was cancelled before it was
  ever suspended.
* Fixed a minor problem with `awaitFirst` on reactive streams that would have resulted in spurious stack-traces printed
  on the console when used with publishers/observables that continue to invoke `onNext` despite being cancelled/disposed 
  (which they are technically allowed to do by specification). 
* All factory functions for various interfaces are implemented as top-level functions
  (affects `Job`, `Channel`, `BroadcastChannel`, `Mutex`, `EventLoop`, and `CoroutineExceptionHandler`). 
  Previous approach of using `operator invoke` on their companion objects is deprecated. 
* Nicer-to-use debug `toString` implementations for coroutine dispatcher tasks and continuations.  
* A default dispatcher for `delay` is rewritten and now shares code with `EventLoopImpl` that is used by 
  `runBlocking`. It internally supports non-default `TimeSource` so that delay-using tests can be written 
  with "virtual time" by replacing their time source for the duration of tests (this feature is not available
  outside of the library).

## Version 0.16

* Coroutines that are scheduled for execution are cancellable by default now
  * `suspendAtomicCancellableCoroutine` function is introduced for funs like
    `send`/`receive`/`receiveOrNull` that require atomic cancellation
    (they cannot be cancelled after decision was made)
  * Coroutines started with default mode using
    `async`/`launch`/`actor` builders can be cancelled before their execution starts
  * `CoroutineStart.ATOMIC` is introduced as a start mode to specify that
    coroutine cannot be cancelled before its execution starts
  * `run` function is also cancellable in the same way and accepts an optional
    `CoroutineStart` parameter to change this default.
* `BroadcastChannel` factory function is introduced
* `CoroutineExceptionHandler` factory function is introduced by @konrad-kaminski
* [`integration`](integration) directory is introduced for all 3rd party integration projects
  * It has [contribution guidelines](integration/README.md#contributing) and contributions from community are welcome
  * Support for Guava `ListenableFuture` in the new [`kotlinx-coroutines-guava`](integration/kotlinx-coroutines-guava) module
  * Rx1 Scheduler support by @konrad-kaminski
* Fixed a number of `Channel` and `BroadcastChannel` implementation bugs related to concurrent 
  send/close/close of channels that lead to hanging send, offer or close operations (see #66). 
  Thanks to @chrisly42 and @cy6erGn0m for finding them.
* Fixed `withTimeoutOrNull` which was returning `null` on timeout of inner or outer `withTimeout` blocks (see #67).
  Thanks to @gregschlom for finding the problem.
* Fixed a bug where `Job` fails to dispose a handler when it is the only handler by @uchuhimo

## Version 0.15

* Switched to Kotlin version 1.1.2 (can still be used with 1.1.0).
* `CoroutineStart` enum is introduced for `launch`/`async`/`actor` builders:
  * The usage of `luanch(context, start = false)` is deprecated and is replaced with 
    `launch(context, CoroutineStart.LAZY)`
  * `CoroutineStart.UNDISPATCHED` is introduced to start coroutine execution immediately in the invoker thread,
     so that `async(context, CoroutineStart.UNDISPATCHED)` is similar to the behavior of C# `async`.
  * [Guide to UI programming with coroutines](ui/coroutines-guide-ui.md) mentions the use of it to optimize
    the start of coroutines from UI threads.
* Introduced `BroadcastChannel` interface in `kotlinx-coroutines-core` module:
  * It extends `SendChannel` interface and provides `open` function to create subscriptions.
  * Subscriptions are represented with `SubscriptionReceiveChannel` interface. 
  * The corresponding `SubscriptionReceiveChannel` interfaces are removed from [reactive](reactive) implementation
     modules. They use an interface defined in `kotlinx-coroutines-core` module.
  * `ConflatedBroadcastChannel` implementation is provided for state-observation-like use-cases, where a coroutine or a
     regular code (in UI, for example) updates the state that subscriber coroutines shall react to.
  * `ArrayBroadcastChannel` implementation is provided for event-bus-like use-cases, where a sequence of events shall
     be received by multiple subscribers without any omissions.
  * [Guide to reactive streams with coroutines](reactive/coroutines-guide-reactive.md) includes 
    "Rx Subject vs BroadcastChannel" section.
* Pull requests from Konrad Kamiński are merged into reactive stream implementations:
  * Support for Project Reactor `Mono` and `Flux`. 
    See [`kotlinx-coroutines-reactor`](reactive/kotlinx-coroutines-reactor) module.
  * Implemented Rx1 `Completable.awaitCompleted`.
  * Added support for Rx2 `Maybe`.
* Better timeout support:  
  * Introduced `withTimeoutOrNull` function.
  * Implemented `onTimeout` clause for `select` expressions.
  * Fixed spurious concurrency inside `withTimeout` blocks on their cancellation. 
  * Changed behavior of `withTimeout` when `CancellationException` is suppressed inside the block. 
    Invocation of `withTimeout` now always returns the result of execution of its inner block.
* The `channel` property in `ActorScope` is promoted to a wider `Channel` type, so that an actor
  can have an easy access to its own inbox send channel.
* Renamed `Mutex.withMutex` to `Mutex.withLock`, old name is deprecated.  

## Version 0.14
 
* Switched to Kotlin version 1.1.1 (can still be used with 1.1.0).
* Introduced `consumeEach` helper function for channels and reactive streams, Rx 1.x, and Rx 2.x.
  * It ensures that streams are unsubscribed from on any exception.
  * Iteration with `for` loop on reactive streams is **deprecated**.
  * [Guide to reactive streams with coroutines](reactive/coroutines-guide-reactive.md) is updated virtually
    all over the place to reflect these important changes.
* Implemented `awaitFirstOrDefault` extension for reactive streams, Rx 1.x, and Rx 2.x.
* Added `Mutex.withMutex` helper function.
* `kotlinx-coroutines-android` module has `provided` dependency on of Android APIs to 
  eliminate warnings when using it in android project.

## Version 0.13

* New `kotlinx-coroutinex-android` module with Android `UI` context implementation. 
* Introduced `whileSelect` convenience function.
* Implemented `ConflatedChannel`.  
* Renamed various `toXXX` conversion functions to `asXXX` (old names are deprecated).
* `run` is optimized with fast-path case and no longer has `CoroutineScope` in its block.
* Fixed dispatching logic of `withTimeout` (removed extra dispatch).
* `EventLoop` that is used by `runBlocking` now implements Delay, giving more predictable test behavior.
* Various refactorings related to resource management and timeouts:
  * `Job.Registration` is renamed to `DisposableHandle`.
  * `EmptyRegistration` is renamed to `NonDisposableHandle`.
  * `Job.unregisterOnCompletion` is renamed to `Job.disposeOnCompletion`.
  * `Delay.invokeOnTimeout` is introduced.
  * `withTimeout` now uses `Delay.invokeOnTimeout` when available.
* A number of improvement for reactive streams and Rx:
  * Introduced `rxFlowable` builder for Rx 2.x.
  * `Scheduler.asCoroutineDispatcher` extension for Rx 2.x.
  * Fixed bug with sometimes missing `onComplete` in `publish`, `rxObservable`, and `rxFlowable` builders.
  * Channels that are open for reactive streams are now `Closeable`.
  * Fixed `CompletableSource.await` and added test for it.
  * Removed `rx.Completable.await` due to name conflict.
* New documentation:
  * [Guide to UI programming with coroutines](ui/coroutines-guide-ui.md)
  * [Guide to reactive streams with coroutines](reactive/coroutines-guide-reactive.md)
* Code is published to JCenter repository.

## Version 0.12

* Switched to Kotlin version 1.1.0 release.
* Reworked and updated utilities for 
  [Reactive Streams](kotlinx-coroutines-reactive), 
  [Rx 1.x](kotlinx-coroutines-rx1), and 
  [Rx 2.x](kotlinx-coroutines-rx2) with library-specific 
  coroutine builders, suspending functions, converters and iteration support.
* `LinkedListChannel` with unlimited buffer (`offer` always succeeds).
* `onLock` select clause and an optional `owner` parameter in all `Mutex` functions.
* `selectUnbiased` function.
* `actor` coroutine builder.
* Couple more examples for "Shared mutable state and concurrency" section and 
  "Channels are fair" section with ping-pong table example 
  in [coroutines guide](coroutines-guide.md).

## Version 0.11-rc

* `select` expression with onJoin/onAwait/onSend/onReceive clauses.
* `Mutex` is moved to `kotlinx.coroutines.experimental.sync` package.
* `ClosedSendChannelException` is a subclass of `CancellationException` now.
* New sections on "Shared mutable state and concurrency" and "Select expression" 
  in [coroutines guide](coroutines-guide.md).

## Version 0.10-rc

* Switched to Kotlin version 1.1.0-rc-91.
* `Mutex` synchronization primitive is introduced.
* `buildChannel` is renamed to `produce`, old name is deprecated.
* `Job.onCompletion` is renamed to `Job.invokeOnCompletion`, old name is deprecated.
* `delay` implementation in Swing, JavaFx, and scheduled executors is fixed to avoid an extra dispatch.
* `CancellableContinuation.resumeUndispatched` is introduced to make this efficient implementation possible.
* Remove unnecessary creation of `CancellationException` to improve performance, plus other performance improvements.
* Suppress deprecated and internal APIs from docs.
* Better docs at top level with categorized summary of classes and functions.

## Version 0.8-beta

* `defer` coroutine builder is renamed to `async`.
* `lazyDefer` is deprecated, `async` has an optional `start` parameter instead.
* `LazyDeferred` interface is deprecated, lazy start functionality is integrated into `Job` interface.
* `launch` has an optional `start` parameter for lazily started coroutines.
* `Job.start` and `Job.isCompleted` are introduced.
* `Deferred.isCompletedExceptionally` and `Deferred.isCancelled` are introduced.
* `Job.getInactiveCancellationException` is renamed to `getCompletionException`.
* `Job.join` is now a member function.
* Internal `JobSupport` state machine is enhanced to support _new_ (not-started-yet) state.
  So, lazy coroutines do not need a separate state variable to track their started/not-started (new/active) status.
* Exception transparency in `Job.cancel` (original cause is rethrown).
* Clarified possible states for `Job`/`CancellableContinuation`/`Deferred` in docs.
* Example on async-style functions and links to API reference site from [coroutines guide](coroutines-guide.md).

## Version 0.7-beta

* Buffered and unbuffered channels are introduced: `Channel`, `SendChannel`, and `ReceiveChannel` interfaces,
  `RendezvousChannel` and `ArrayChannel` implementations, `Channel()` factory function and `buildChannel{}`
  coroutines builder.
* `Here` context is renamed to `Unconfined` (the old name is deprecated).
* A [guide on coroutines](coroutines-guide.md) is expanded: sections on contexts and channels.  
 
## Version 0.6-beta

* Switched to Kotlin version 1.1.0-beta-37.
* A [guide on coroutines](coroutines-guide.md) is expanded.  

## Version 0.5-beta

* Switched to Kotlin version 1.1.0-beta-22 (republished version).
* Removed `currentCoroutineContext` and related thread-locals without replacement.
  Explicitly pass coroutine context around if needed.
* `lazyDefer(context) {...}` coroutine builder and `LazyDeferred` interface are introduced.
* The default behaviour of all coroutine dispatchers is changed to always schedule execution of new coroutine 
  for later in this thread or thread pool. Correspondingly, `CoroutineDispatcher.isDispatchNeeded` function
  has a default implementation that returns `true`.
* `NonCancellable` context is introduced.  
* Performance optimizations for cancellable continuations (fewer objects created).
* A [guide on coroutines](coroutines-guide.md) is added.  

## Version 0.4-beta

* Switched to Kotlin version 1.1.0-beta-18 (republished version).
* `CoroutineDispatcher` methods now have `context` parameter.
* Introduced `CancellableContinuation.isCancelled`
* Introduced `EventLoop` dispatcher and made it a default for `runBlocking { ... }`
* Introduced `CoroutineScope` interface with `isActive` and `context` properties; 
  standard coroutine builders include it as receiver for convenience.
* Introduced `Executor.toCoroutineDispatcher()` extension.  
* Delay scheduler thread is not daemon anymore, but times out automatically.
* Debugging facilities in `newCoroutineContext` can be explicitly disabled with `-Dkotlinx.coroutines.debug=off`.
* xxx-test files are renamed to xxx-example for clarity.
* Fixed NPE in Job implementation when starting coroutine with already cancelled parent job.
* Support cancellation in `kotlinx-coroutines-nio` module
