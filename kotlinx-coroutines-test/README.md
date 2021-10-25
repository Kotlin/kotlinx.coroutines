# Module kotlinx-coroutines-test

Test utilities for `kotlinx.coroutines`.

## Overview

This package provides utilities for efficiently testing coroutines.

| Name | Description |
| ---- | ----------- |
| [runTest] | Runs the test code, automatically skipping delays and handling uncaught exceptions. |
| [TestCoroutineScheduler] | The shared source of virtual time, used for controlling execution order and skipping delays. |
| [TestScope] | A [CoroutineScope] that integrates with [runTest], providing access to [TestCoroutineScheduler]. |
| [TestDispatcher] | A [CoroutineDispatcher] that whose delays are controlled by a [TestCoroutineScheduler]. |
| [Dispatchers.setMain] | Mocks the main dispatcher using the provided one. If mocked with a [TestDispatcher], its [TestCoroutineScheduler] is used everywhere by default. |

Provided [TestDispatcher] implementations:

| Name | Description |
| ---- | ----------- |
| [StandardTestDispatcher] | A simple dispatcher with no special behavior other than being linked to a [TestCoroutineScheduler]. |
| [UnconfinedTestDispatcher] | A dispatcher that behaves like [Dispatchers.Unconfined]. |

## Using in your project

Add `kotlinx-coroutines-test` to your project test dependencies:
```
dependencies {
    testImplementation 'org.jetbrains.kotlinx:kotlinx-coroutines-test:1.5.2'
}
```

**Do not** depend on this project in your main sources, all utilities here are intended and designed to be used only from tests.

## Dispatchers.Main Delegation

`Dispatchers.setMain` will override the `Main` dispatcher in test scenarios.
This is helpful when one wants to execute a test in situations where the platform `Main` dispatcher is not available,
or to replace `Dispatchers.Main` with a testing dispatcher.

On the JVM,
the [`ServiceLoader`](https://docs.oracle.com/javase/8/docs/api/java/util/ServiceLoader.html) mechanism is responsible
for overwriting [Dispatchers.Main] with a testable implementation, which by default will delegate its calls to the real
`Main` dispatcher, if any.

The `Main` implementation can be overridden using [setMain][setMain] method with any [CoroutineDispatcher]
implementation, e.g.:

```kotlin

class SomeTest {

    private val mainThreadSurrogate = newSingleThreadContext("UI thread")

    @Before
    fun setUp() {
        Dispatchers.setMain(mainThreadSurrogate)
    }

    @After
    fun tearDown() {
        Dispatchers.resetMain() // reset the main dispatcher to the original Main dispatcher
        mainThreadSurrogate.close()
    }

    @Test
    fun testSomeUI() = runBlocking {
        launch(Dispatchers.Main) {  // Will be launched in the mainThreadSurrogate dispatcher
            // ...
        }
    }
}
```

Calling `setMain` or `resetMain` immediately changes the `Main` dispatcher globally.

If `Main` is overridden with a [TestDispatcher], then its [TestCoroutineScheduler] is used when new [TestDispatcher] or
[TestScope] instances are created without [TestCoroutineScheduler] being passed as an argument.

## runTest

[runTest] is the way to test code that involves coroutines. `suspend` functions can be called inside it.

**IMPORTANT: in order to work with on Kotlin/JS, the result of `runTest` must be immediately `return`-ed from each test.**
The typical invocation of [runTest] thus looks like this:

```kotlin
@Test
fun testFoo() = runTest {
    // code under test
}
```

In more advanced scenarios, it's possible instead to use the following form:
```kotlin
@Test
fun testFoo(): TestResult {
    // initialize some test state
    return runTest {
        // code under test
    }
}
```

[runTest] is similar to running the code with `runBlocking` on Kotlin/JVM and Kotlin/Native, or launching a new promise
on Kotlin/JS. The main differences are the following:

* **The calls to `delay` are automatically skipped**, preserving the relative execution order of the tasks. This way,
  it's possible to make tests finish more-or-less immediately.
* **Controlling the virtual time**: in case just skipping delays is not sufficient, it's possible to more carefully
  guide the execution, advancing the virtual time by a duration, draining the queue of the awaiting tasks, or running
  the tasks scheduled at the present moment.
* **Handling uncaught exceptions** spawned in the child coroutines by throwing them at the end of the test.
* **Detecting unfinished jobs**, that is, tasks that are still pending by the end of the test, in order to prevent
  coroutine leaks.
* **Waiting for asynchronous callbacks**.
  Sometimes, especially when working with third-party code, it's impossible to mock all the dispatchers in use.
  [runTest] will handle the situations where some code runs in dispatchers not enhanced by the test module.

### Delay-skipping

To test regular suspend functions, which may have a delay, .

```kotlin
@Test
fun testFoo() = runBlockingTest { // a coroutine with an extra test control
    val actual = foo()
    // ...
}

suspend fun foo() {
    delay(1_000) // auto-advances virtual time by 1_000ms due to runBlockingTest
    // ...
}
```

### Eagerly entering `launch` and `async` blocks

### Child coroutine behavior

Unless they use a different [ContinuationInterceptor], all the coroutines launched in [runTest] will be executed on the
test thread. In order to decide which code to execute next,

### Delay-skipping

If the coroutine created by `launch` or `async` calls `delay` then the [runBlockingTest] will not auto-progress time
right away. This allows tests to observe the interaction of multiple coroutines with different delays.

To control time in the test you can use the [DelayController] interface. The block passed to
[runBlockingTest] can call any method on the `DelayController` interface.

```kotlin
@Test
fun testFooWithLaunchAndDelay() = runBlockingTest {
    foo()
    // the coroutine launched by foo has not completed here, it is suspended waiting for delay(1_000)
    advanceTimeBy(1_000) // progress time, this will cause the delay to resume
    // the coroutine launched by foo has completed here
    // ...
}

suspend fun CoroutineScope.foo() {
    launch {
        println(1)   // executes eagerly when foo() is called due to runBlockingTest
        delay(1_000) // suspends until time is advanced by at least 1_000
        println(2)   // executes after advanceTimeBy(1_000)
    }
}
```

*Note:* `runBlockingTest` will always attempt to auto-progress time until all coroutines are completed just before
exiting. This is a convenience to avoid having to call [advanceUntilIdle][DelayController.advanceUntilIdle]
as the last line of many common test cases.
If any coroutines cannot complete by advancing time, an `AssertionError` is thrown.

## Test coroutine scope

Structured concurrency ties coroutines to scopes in which they are launched.
[TestScope] is a special coroutine scope designed for testing coroutines. A new [TestScope] is automatically created
for [runTest]; however, it's possible to access this scope even before the test has started, in order to initialize all
the data structures for testing, probably to perform some mocking.

```kotlin
val testScope = TestScope()

@BeforeTest
fun initialize() {
    mainAppScope.mock(testScope)
}

@Test
fun testFoo() = testScope.runTest {
    // the receiver here is the same scope as `testScope`
}
```

## Structured concurrency integration


### Controlling the virtual time

### Handling the child coroutine failures

### Detecting unfinished jobs

## Test coroutine scheduler

When using entities from this module to test code, the delays

This module introduces [TestCoroutineScheduler], as well as the dispatchers [StandardTestDispatcher] and
[UnconfinedTestDispatcher], each instance of which is linked to some [TestCoroutineScheduler].

## runBlockingTest

To test regular suspend functions or coroutines started with `launch` or `async` use the [runBlockingTest] coroutine
builder that provides extra test control to coroutines.

1. Auto-advancing of time for regular suspend functions
2. Explicit time control for testing multiple coroutines
3. Eager execution of `launch` or `async` code blocks
4. Pause, manually advance, and restart the execution of coroutines in a test
5. Report uncaught exceptions as test failures

### Testing regular suspend functions

To test regular suspend functions, which may have a delay, you can use the [runBlockingTest] builder to start a testing
coroutine. Any calls to `delay` will automatically advance virtual time by the amount delayed.

```kotlin
@Test
fun testFoo() = runBlockingTest { // a coroutine with an extra test control
    val actual = foo()
    // ...
}

suspend fun foo() {
    delay(1_000) // auto-advances virtual time by 1_000ms due to runBlockingTest
    // ...
}
```

`runBlockingTest` returns `Unit` so it may be used in a single expression with common testing libraries.

### Testing `launch` or `async`

Inside of [runBlockingTest], both [launch] and [async] will start a new coroutine that may run concurrently with the
test case.

To make common testing situations easier, by default the body of the coroutine is executed *eagerly* until
the first call to [delay] or [yield].

```kotlin
@Test
fun testFooWithLaunch() = runBlockingTest {
    foo()
    // the coroutine launched by foo() is completed before foo() returns
    // ...
}

fun CoroutineScope.foo() {
     // This coroutines `Job` is not shared with the test code
     launch {
         bar()      // executes eagerly when foo() is called due to runBlockingTest
         println(1) // executes eagerly when foo() is called due to runBlockingTest
     }
}

suspend fun bar() {}
```

`runBlockingTest` will auto-progress virtual time until all coroutines are completed before returning. If any coroutines
are not able to complete, an `AssertionError` will be thrown.

*Note:* The default eager behavior of [runBlockingTest] will ignore [CoroutineStart] parameters.

### Testing `launch` or `async` with `delay`

If the coroutine created by `launch` or `async` calls `delay` then the [runBlockingTest] will not auto-progress time
right away. This allows tests to observe the interaction of multiple coroutines with different delays.

To control time in the test you can use the [DelayController] interface. The block passed to
[runBlockingTest] can call any method on the `DelayController` interface.

```kotlin
@Test
fun testFooWithLaunchAndDelay() = runBlockingTest {
    foo()
    // the coroutine launched by foo has not completed here, it is suspended waiting for delay(1_000)
    advanceTimeBy(1_000) // progress time, this will cause the delay to resume
    // the coroutine launched by foo has completed here
    // ...
}

suspend fun CoroutineScope.foo() {
    launch {
        println(1)   // executes eagerly when foo() is called due to runBlockingTest
        delay(1_000) // suspends until time is advanced by at least 1_000
        println(2)   // executes after advanceTimeBy(1_000)
    }
}
```

*Note:* `runBlockingTest` will always attempt to auto-progress time until all coroutines are completed just before
exiting. This is a convenience to avoid having to call [advanceUntilIdle][DelayController.advanceUntilIdle]
as the last line of many common test cases.
If any coroutines cannot complete by advancing time, an `AssertionError` is thrown.

### Testing `withTimeout` using `runBlockingTest`

Time control can be used to test timeout code. To do so, ensure that the function under test is suspended inside a
`withTimeout` block and advance time until the timeout is triggered.

Depending on the code, causing the code to suspend may need to use different mocking or fake techniques. For this
example an uncompleted `Deferred<Foo>` is provided to the function under test via parameter injection.

```kotlin
@Test(expected = TimeoutCancellationException::class)
fun testFooWithTimeout() = runBlockingTest {
    val uncompleted = CompletableDeferred<Foo>() // this Deferred<Foo> will never complete
    foo(uncompleted)
    advanceTimeBy(1_000) // advance time, which will cause the timeout to throw an exception
    // ...
}

fun CoroutineScope.foo(resultDeferred: Deferred<Foo>) {
    launch {
        withTimeout(1_000) {
            resultDeferred.await() // await() will suspend forever waiting for uncompleted
            // ...
        }
    }
}
```

*Note:* Testing timeouts is simpler with a second coroutine that can be suspended (as in this example). If the
call to `withTimeout` is in a regular suspend function, consider calling `launch` or `async` inside your test body to
create a second coroutine.

### Using `pauseDispatcher` for explicit execution of `runBlockingTest`

The eager execution of `launch` and `async` bodies makes many tests easier, but some tests need more fine grained
control of coroutine execution.

To disable eager execution, you can call [pauseDispatcher][DelayController.pauseDispatcher]
to pause the [TestCoroutineDispatcher] that [runBlockingTest] uses.

When the dispatcher is paused, all coroutines will be added to a queue instead running. In addition, time will never
auto-progress due to `delay` on a paused dispatcher.

```kotlin
@Test
fun testFooWithPauseDispatcher() = runBlockingTest {
    pauseDispatcher {
        foo()
        // the coroutine started by foo has not run yet
        runCurrent() // the coroutine started by foo advances to delay(1_000)
        // the coroutine started by foo has called println(1), and is suspended on delay(1_000)
        advanceTimeBy(1_000) // progress time, this will cause the delay to resume
        // the coroutine started by foo has called println(2) and has completed here
    }
    // ...
}

fun CoroutineScope.foo() {
    launch {
        println(1)   // executes after runCurrent() is called
        delay(1_000) // suspends until time is advanced by at least 1_000
        println(2)   // executes after advanceTimeBy(1_000)
    }
}
```

Using `pauseDispatcher` gives tests explicit control over the progress of time as well as the ability to enqueue all
coroutines. As a best practice consider adding two tests, one paused and one eager, to test coroutines that have
non-trivial external dependencies and side effects in their launch body.

*Important:* When passed a lambda block, `pauseDispatcher` will resume eager execution immediately after the block.
This will cause time to auto-progress if there are any outstanding `delay` calls that were not resolved before the
`pauseDispatcher` block returned. In advanced situations tests can call [pauseDispatcher][DelayController.pauseDispatcher]
without a lambda block and then explicitly resume the dispatcher with [resumeDispatcher][DelayController.resumeDispatcher].

## Integrating tests with structured concurrency

Code that uses structured concurrency needs a [CoroutineScope] in order to launch a coroutine. In order to integrate
[runBlockingTest] with code that uses common structured concurrency patterns tests can provide one (or both) of these
classes to application code.

 | Name | Description |
 | ---- | ----------- |
 | [TestCoroutineScope] | A [CoroutineScope] which provides detailed control over the execution of coroutines for tests and integrates with [runBlockingTest]. |
 | [TestCoroutineDispatcher] | A [CoroutineDispatcher] which can be used for tests and integrates with [runBlockingTest]. |

 Both classes are provided to allow for various testing needs. Depending on the code that's being
 tested, it may be easier to provide a [TestCoroutineDispatcher]. For example [Dispatchers.setMain][setMain] will accept
 a [TestCoroutineDispatcher] but not a [TestCoroutineScope].

 [TestCoroutineScope] will always use a [TestCoroutineDispatcher] to execute coroutines. It
 also uses [TestCoroutineExceptionHandler] to convert uncaught exceptions into test failures.

By providing [TestCoroutineScope] a test case is able to control execution of coroutines, as well as ensure that
uncaught exceptions thrown by coroutines are converted into test failures.

### Providing [TestScope] from [runTest]

In simple cases, tests can use the [TestScope] created by [runTest] directly.

```kotlin
@Test
fun testFoo() = runTest { // the receiver of this block is a TestScope
    foo()
}

fun CoroutineScope.foo() {
    launch { // CoroutineScope is the TestCoroutineScope provided by runTest
        // ...
    }
}
```

This style is preferred when the `CoroutineScope` is passed through an extension function style.

### Providing an explicit [TestScope]

In many cases, the direct style is not preferred because [CoroutineScope] may need to be provided through another means
such as dependency injection or service locators.

Tests can create a [TestScope] in advance to support these use cases.

[TestScope] on its own does not automatically run the code launched in it.
In addition, it is stateful in order to keep track of executing coroutines and uncaught exceptions.
Therefore, it is important to ensure that [TestScope.runTest] is called eventually.

```kotlin
class TestClass {
    private val testScope = TestScope()
    private lateinit var subject: Subject

    @Before
    fun setup() {
        // provide the scope explicitly, in this example using a constructor parameter
        subject = Subject(testScope)
    }

    @Test
    fun testFoo() = testScope.runTest { // the receiver here is `testScope`
        subject.foo()
    }
}

class Subject(val scope: CoroutineScope) {
    fun foo() {
        scope.launch {
            // launch uses the testScope injected in setup
        }
    }
}
```

## Virtual time control with other dispatchers

Calls to `withContext(Dispatchers.IO)`, `withContext(Dispatchers.Default)` ,and `withContext(Dispatchers.Main)` are
common in coroutines-based code bases. Unfortunately, just executing code in a test will not lead to these dispatchers
using the virtual time source, so delays will not be skipped in them.

```kotlin
suspend fun veryExpensiveFunction() = withContext(Dispatchers.Default) {
    delay(1_000)
    1
}

fun testExpensiveFunction() = runTest {
    val result = veryExpensiveFunction() // will take a whole real-time second to execute
    // the virtual time at this point is still 0
}
```

Tests should, when possible, replace these dispatchers with a [TestDispatcher] if the `withContext` calls `delay` in the
function under test. For example, `veryExpensiveFunction` above should allow mocking with a [TestDispatcher] using
either dependency injection, a service locator, or a default parameter, if it is to be used with virtual time.

### Status of the API

This API is experimental and it is may change before migrating out of experimental (while it is marked as
[`@ExperimentalCoroutinesApi`][ExperimentalCoroutinesApi]).
Changes during experimental may have deprecation applied when possible, but it is not
advised to use the API in stable code before it leaves experimental due to possible breaking changes.

If you have any suggestions for improvements to this experimental API please share them them on the
[issue tracker](https://github.com/Kotlin/kotlinx.coroutines/issues).

<!--- MODULE kotlinx-coroutines-core -->
<!--- INDEX kotlinx.coroutines -->

[CoroutineScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-coroutine-scope/index.html
[CoroutineDispatcher]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-coroutine-dispatcher/index.html
[Dispatchers.Unconfined]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-dispatchers/-unconfined.html
[Dispatchers.Main]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-dispatchers/-main.html
[launch]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/launch.html
[async]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/async.html
[delay]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/delay.html
[yield]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/yield.html
[CoroutineStart]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-coroutine-start/index.html
[ExperimentalCoroutinesApi]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-experimental-coroutines-api/index.html

<!--- MODULE kotlinx-coroutines-test -->
<!--- INDEX kotlinx.coroutines.test -->

[runTest]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-test/kotlinx.coroutines.test/run-test.html
[TestCoroutineScheduler]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-test/kotlinx.coroutines.test/-test-coroutine-scheduler/index.html
[TestScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-test/kotlinx.coroutines.test/-test-scope/index.html
[TestDispatcher]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-test/kotlinx.coroutines.test/-test-dispatcher/index.html
[Dispatchers.setMain]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-test/kotlinx.coroutines.test/set-main.html
[StandardTestDispatcher]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-test/kotlinx.coroutines.test/-standard-test-dispatcher.html
[UnconfinedTestDispatcher]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-test/kotlinx.coroutines.test/-unconfined-test-dispatcher.html
[setMain]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-test/kotlinx.coroutines.test/set-main.html
[runBlockingTest]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-test/kotlinx.coroutines.test/run-blocking-test.html
[DelayController]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-test/kotlinx.coroutines.test/-delay-controller/index.html
[DelayController.advanceUntilIdle]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-test/kotlinx.coroutines.test/-delay-controller/advance-until-idle.html
[DelayController.pauseDispatcher]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-test/kotlinx.coroutines.test/-delay-controller/pause-dispatcher.html
[TestCoroutineDispatcher]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-test/kotlinx.coroutines.test/-test-coroutine-dispatcher/index.html
[DelayController.resumeDispatcher]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-test/kotlinx.coroutines.test/-delay-controller/resume-dispatcher.html
[TestCoroutineScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-test/kotlinx.coroutines.test/-test-coroutine-scope/index.html
[TestCoroutineExceptionHandler]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-test/kotlinx.coroutines.test/-test-coroutine-exception-handler/index.html
[TestScope.runTest]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-test/kotlinx.coroutines.test/run-test.html

<!--- END -->
