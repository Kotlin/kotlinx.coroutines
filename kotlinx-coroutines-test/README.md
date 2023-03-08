# Module kotlinx-coroutines-test

Test utilities for `kotlinx.coroutines`.

## Overview

This package provides utilities for efficiently testing coroutines.

| Name | Description |
| ---- | ----------- |
| [runTest] | Runs the test code, automatically skipping delays and handling uncaught exceptions. |
| [TestCoroutineScheduler] | The shared source of virtual time, used for controlling execution order and skipping delays. |
| [TestScope] | A [CoroutineScope] that integrates with [runTest], providing access to [TestCoroutineScheduler]. |
| [TestDispatcher] | A [CoroutineDispatcher] whose delays are controlled by a [TestCoroutineScheduler]. |
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
    testImplementation 'org.jetbrains.kotlinx:kotlinx-coroutines-test:1.7.0-Beta'
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

The `Main` implementation can be overridden using [Dispatchers.setMain][setMain] method with any [CoroutineDispatcher]
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
* **The execution times out after 10 seconds**, cancelling the test coroutine to prevent tests from hanging forever 
  and eating up the CI resources.
* **Controlling the virtual time**: in case just skipping delays is not sufficient, it's possible to more carefully
  guide the execution, advancing the virtual time by a duration, draining the queue of the awaiting tasks, or running
  the tasks scheduled at the present moment.
* **Handling uncaught exceptions** spawned in the child coroutines by throwing them at the end of the test.
* **Waiting for asynchronous callbacks**.
  Sometimes, especially when working with third-party code, it's impossible to mock all the dispatchers in use.
  [runTest] will handle the situations where some code runs in dispatchers not integrated with the test module.

## Timeout

Test automatically time out after 10 seconds. For example, this test will fail with a timeout exception:

```kotlin
@Test
fun testHanging() = runTest {
    CompletableDeferred<Unit>().await() // will hang forever
}
```

In case the test is expected to take longer than 10 seconds, the timeout can be increased by passing the `timeout`
parameter:

```kotlin
@Test
fun testTakingALongTime() = runTest(timeout = 30.seconds) {
    val result = withContext(Dispatchers.Default) {
        delay(20.seconds) // this delay is not in the test dispatcher and will not be skipped
        3
    }
    assertEquals(3, result)
}
```

## Delay-skipping

To test regular suspend functions, which may have a delay, just run them inside the [runTest] block.

```kotlin
@Test
fun testFoo() = runTest { // a coroutine with an extra test control
    val actual = foo()
    // ...
}

suspend fun foo() {
    delay(1_000) // when run in `runTest`, will finish immediately instead of delaying
    // ...
}
```

## `launch` and `async`

The coroutine dispatcher used for tests is single-threaded, meaning that the child coroutines of the [runTest] block
will run on the thread that started the test, and will never run in parallel.

If several coroutines are waiting to be executed next, the one scheduled after the smallest delay will be chosen.
The virtual time will automatically advance to the point of its resumption.

```kotlin
@Test
fun testWithMultipleDelays() = runTest {
    launch {
        delay(1_000)
        println("1. $currentTime") // 1000
        delay(200)
        println("2. $currentTime") // 1200
        delay(2_000)
        println("4. $currentTime") // 3200
    }
    val deferred = async {
        delay(3_000)
        println("3. $currentTime") // 3000
        delay(500)
        println("5. $currentTime") // 3500
    }
    deferred.await()
}
```

## Controlling the virtual time

Inside [runTest], the execution is scheduled by [TestCoroutineScheduler], which is a virtual time scheduler.
The scheduler has several special methods that allow controlling the virtual time:
* `currentTime` gets the current virtual time.
* `runCurrent()` runs the tasks that are scheduled at this point of virtual time.
* `advanceUntilIdle()` runs all enqueued tasks until there are no more.
* `advanceTimeBy(timeDelta)` runs the enqueued tasks until the current virtual time advances by `timeDelta`.
* `timeSource` returns a `TimeSource` that uses the virtual time.

```kotlin
@Test
fun testFoo() = runTest {
    launch {
        val workDuration = testScheduler.timeSource.measureTime {
            println(1)   // executes during runCurrent()
            delay(1_000) // suspends until time is advanced by at least 1_000
            println(2)   // executes during advanceTimeBy(2_000)
            delay(500)   // suspends until the time is advanced by another 500 ms
            println(3)   // also executes during advanceTimeBy(2_000)
            delay(5_000) // will suspend by another 4_500 ms
            println(4)   // executes during advanceUntilIdle()
        }
        assertEquals(6500.milliseconds, workDuration) // the work took 6_500 ms of virtual time
    }
    // the child coroutine has not run yet
    testScheduler.runCurrent()
    // the child coroutine has called println(1), and is suspended on delay(1_000)
    testScheduler.advanceTimeBy(2.seconds) // progress time, this will cause two calls to `delay` to resume
    // the child coroutine has called println(2) and println(3) and suspends for another 4_500 virtual milliseconds
    testScheduler.advanceUntilIdle() // will run the child coroutine to completion
    assertEquals(6500, currentTime) // the child coroutine finished at virtual time of 6_500 milliseconds
}
```

## Using multiple test dispatchers

The virtual time is controlled by an entity called the [TestCoroutineScheduler], which behaves as the shared source of
virtual time.

Several dispatchers can be created that use the same [TestCoroutineScheduler], in which case they will share their
knowledge of the virtual time.

To access the scheduler used for this test, use the [TestScope.testScheduler] property.

```kotlin
@Test
fun testWithMultipleDispatchers() = runTest {
        val scheduler = testScheduler // the scheduler used for this test
        val dispatcher1 = StandardTestDispatcher(scheduler, name = "IO dispatcher")
        val dispatcher2 = StandardTestDispatcher(scheduler, name = "Background dispatcher")
        launch(dispatcher1) {
            delay(1_000)
            println("1. $currentTime") // 1000
            delay(200)
            println("2. $currentTime") // 1200
            delay(2_000)
            println("4. $currentTime") // 3200
        }
        val deferred = async(dispatcher2) {
            delay(3_000)
            println("3. $currentTime") // 3000
            delay(500)
            println("5. $currentTime") // 3500
        }
        deferred.await()
    }
```

**Note: if [Dispatchers.Main] is replaced by a [TestDispatcher], [runTest] will automatically use its scheduler.
This is done so that there is no need to go through the ceremony of passing the correct scheduler to [runTest].**

## Accessing the test coroutine scope

Structured concurrency ties coroutines to scopes in which they are launched.
[TestScope] is a special coroutine scope designed for testing coroutines, and a new one is automatically created
for [runTest] and used as the receiver for the test body.

However, it can be convenient to access a `CoroutineScope` before the test has started, for example, to perform mocking
of some
parts of the system in `@BeforeTest` via dependency injection.
In these cases, it is possible to manually create [TestScope], the scope for the test coroutines, in advance,
before the test begins.

[TestScope] on its own does not automatically run the code launched in it.
In addition, it is stateful in order to keep track of executing coroutines and uncaught exceptions.
Therefore, it is important to ensure that [TestScope.runTest] is called eventually.

```kotlin
val scope = TestScope()

@BeforeTest
fun setUp() {
    Dispatchers.setMain(StandardTestDispatcher(scope.testScheduler))
    TestSubject.setScope(scope)
}

@AfterTest
fun tearDown() {
    Dispatchers.resetMain()
    TestSubject.resetScope()
}

@Test
fun testSubject() = scope.runTest {
    // the receiver here is `testScope`
}
```

## Running background work

Sometimes, the fact that [runTest] waits for all the coroutines to finish is undesired.
For example, the system under test may need to receive data from coroutines that always run in the background.
Emulating such coroutines by launching them from the test body is not sufficient, because [runTest] will wait for them
to finish, which they never typically do.

For these cases, there is a special coroutine scope: [TestScope.backgroundScope].
Coroutines launched in it will be cancelled at the end of the test.

```kotlin
@Test
fun testExampleBackgroundJob() = runTest {
  val channel = Channel<Int>()
  backgroundScope.launch {
    var i = 0
    while (true) {
      channel.send(i++)
    }
  }
  repeat(100) {
    assertEquals(it, channel.receive())
  }
}
```

## Eagerly entering `launch` and `async` blocks

Some tests only test functionality and don't particularly care about the precise order in which coroutines are
dispatched.
In these cases, it can be cumbersome to always call [runCurrent] or [yield] to observe the effects of the coroutines
after they are launched.

If [runTest] executes with an [UnconfinedTestDispatcher], the child coroutines launched at the top level are entered
*eagerly*, that is, they don't go through a dispatch until the first suspension.

```kotlin
@Test
fun testEagerlyEnteringChildCoroutines() = runTest(UnconfinedTestDispatcher()) {
    var entered = false
    val deferred = CompletableDeferred<Unit>()
    var completed = false
    launch {
        entered = true
        deferred.await()
        completed = true
    }
    assertTrue(entered) // `entered = true` already executed.
    assertFalse(completed) // however, the child coroutine then suspended, so it is enqueued.
    deferred.complete(Unit) // resume the coroutine.
    assertTrue(completed) // now the child coroutine is immediately completed.
}
```

If this behavior is desirable, but some parts of the test still require accurate dispatching, for example, to ensure
that the code executes on the correct thread, then simply `launch` a new coroutine with the [StandardTestDispatcher].

```kotlin
@Test
fun testEagerlyEnteringSomeChildCoroutines() = runTest(UnconfinedTestDispatcher()) {
    var entered1 = false
    launch {
        entered1 = true
    }
    assertTrue(entered1) // `entered1 = true` already executed

    var entered2 = false
    launch(StandardTestDispatcher(testScheduler)) {
        // this block and every coroutine launched inside it will explicitly go through the needed dispatches
        entered2 = true
    }
    assertFalse(entered2)
    runCurrent() // need to explicitly run the dispatched continuation
    assertTrue(entered2)
}
```

### Using `withTimeout` inside `runTest`

Timeouts are also susceptible to time control, so the code below will immediately finish.

```kotlin
@Test
fun testFooWithTimeout() = runTest {
    assertFailsWith<TimeoutCancellationException> {
        withTimeout(1_000) {
            delay(999)
            delay(2)
            println("this won't be reached")
        }
    }
}
```

## Virtual time support with other dispatchers

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

Many parts of the API is experimental, and it is may change before migrating out of experimental (while it is marked as
[`@ExperimentalCoroutinesApi`][ExperimentalCoroutinesApi]).
Changes during experimental may have deprecation applied when possible, but it is not
advised to use the API in stable code before it leaves experimental due to possible breaking changes.

If you have any suggestions for improvements to this experimental API please share them on the
[issue tracker](https://github.com/Kotlin/kotlinx.coroutines/issues).

<!--- MODULE kotlinx-coroutines-core -->
<!--- INDEX kotlinx.coroutines -->

[CoroutineScope]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-coroutine-scope/index.html
[CoroutineDispatcher]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-coroutine-dispatcher/index.html
[Dispatchers.Unconfined]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-dispatchers/-unconfined.html
[Dispatchers.Main]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-dispatchers/-main.html
[yield]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/yield.html
[ExperimentalCoroutinesApi]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-experimental-coroutines-api/index.html

<!--- MODULE kotlinx-coroutines-test -->
<!--- INDEX kotlinx.coroutines.test -->

[runTest]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-test/kotlinx.coroutines.test/run-test.html
[TestCoroutineScheduler]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-test/kotlinx.coroutines.test/-test-coroutine-scheduler/index.html
[TestScope]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-test/kotlinx.coroutines.test/-test-scope/index.html
[TestDispatcher]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-test/kotlinx.coroutines.test/-test-dispatcher/index.html
[Dispatchers.setMain]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-test/kotlinx.coroutines.test/set-main.html
[StandardTestDispatcher]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-test/kotlinx.coroutines.test/-standard-test-dispatcher.html
[UnconfinedTestDispatcher]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-test/kotlinx.coroutines.test/-unconfined-test-dispatcher.html
[setMain]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-test/kotlinx.coroutines.test/set-main.html
[TestScope.testScheduler]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-test/kotlinx.coroutines.test/-test-scope/test-scheduler.html
[TestScope.runTest]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-test/kotlinx.coroutines.test/run-test.html
[TestScope.backgroundScope]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-test/kotlinx.coroutines.test/-test-scope/background-scope.html
[runCurrent]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-test/kotlinx.coroutines.test/run-current.html

<!--- END -->
