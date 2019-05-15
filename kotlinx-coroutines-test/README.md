# Module kotlinx-coroutines-test

Test utilities for `kotlinx.coroutines`.

This package provides testing utilities for effectively testing coroutines.

## Using in your project

Add `kotlinx-coroutines-test` to your project test dependencies:
```
dependencies {
    testImplementation 'org.jetbrains.kotlinx:kotlinx-coroutines-test:1.2.1'
}
```

**Do not** depend on this project in your main sources, all utilities are intended and designed to be used only from tests.

## Dispatchers.Main Delegation

`Dispatchers.setMain` will override the `Main` dispatcher in test situations. This is helpful when you want to execute a
test in situations where the platform `Main` dispatcher is not available, or you wish to replace `Dispatchers.Main` with a
testing dispatcher.

Once you have this dependency in the runtime,
[`ServiceLoader`](https://docs.oracle.com/javase/8/docs/api/java/util/ServiceLoader.html) mechanism will overwrite
[Dispatchers.Main] with a testable implementation.

You can override the `Main` implementation using [setMain][setMain] method with any [CoroutineDispatcher] implementation, e.g.:

```kotlin

class SomeTest {
    
    private val mainThreadSurrogate = newSingleThreadContext("UI thread")

    @Before
    fun setUp() {
        Dispatchers.setMain(mainThreadSurrogate)
    }

    @After
    fun tearDown() {
        Dispatchers.resetMain() // reset main dispatcher to the original Main dispatcher
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
Calling `setMain` or `resetMain` immediately changes the `Main` dispatcher globally. The testable version of 
`Dispatchers.Main` installed by the `ServiceLoader` will delegate to the dispatcher provided by `setMain`.

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
coroutine. Any calls to `delay` will automatically advance time.

```kotlin
@Test
fun testFoo() = runBlockingTest { // a coroutine with an extra test control
    val actual = foo() 
    // ...
}

suspend fun foo() {
    delay(1_000) // auto-advances without delay due to runBlockingTest
    // ...
}
```

`runBlockingTest` returns `Unit` so it may be used in a single expression with common testing libraries.

### Testing `launch` or `async`

Inside of [runBlockingTest], both [launch] and [async] will start a new coroutine that may run concurrently with the 
test case. 

To make common testing situations easier, by default the body of the coroutine is executed *eagerly* until 
the first [delay].

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

`runBlockingTest` will auto-progress time until all coroutines are completed before returning. If any coroutines are not
able to complete, an [UncompletedCoroutinesError] will be thrown.

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
    // foo() coroutine launched by foo has completed here
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
If any coroutines cannot complete by advancing time, an [UncompletedCoroutinesError] is thrown.

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

### Providing `TestCoroutineScope` from `runBlockingTest`

In simple cases, tests can use the [TestCoroutineScope] created by [runBlockingTest] directly.

```kotlin
@Test
fun testFoo() = runBlockingTest {        
    foo() // runBlockingTest passed in a TestCoroutineScope as this
}

fun CoroutineScope.foo() {
    launch {  // CoroutineScope for launch is the TestCoroutineScope provided by runBlockingTest
        // ...
    }
}
```

This style is preferred when the `CoroutineScope` is passed through an extension function style.

### Providing an explicit `TestCoroutineScope`

In many cases, the direct style is not preferred because [CoroutineScope] may need to be provided through another means 
such as dependency injection or service locators.

Tests can declare a [TestCoroutineScope] explicitly in the class to support these use cases.

Since [TestCoroutineScope] is stateful in order to keep track of executing coroutines and uncaught exceptions, it is 
important to ensure that [cleanupTestCoroutines][TestCoroutineScope.cleanupTestCoroutines] is called after every test case. 

```kotlin
class TestClass {
    private val testScope = TestCoroutineScope()
    private lateinit var subject: Subject = null 
    
    @Before
    fun setup() {
        // provide the scope explicitly, in this example using a constructor parameter
        subject = Subject(testScope)
    }
    
    @After
    fun cleanUp() {
        testScope.cleanupTestCoroutines()
    }
    
    @Test
    fun testFoo() = testScope.runBlockingTest {
        // TestCoroutineScope.runBlockingTest uses the Dispatcher and exception handler provided by `testScope`
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

*Note:* [TestCoroutineScope], [TestCoroutineDispatcher], and [TestCoroutineExceptionHandler] are interfaces to enable 
test libraries to provide library specific integrations. For example, a JUnit4 `@Rule` may call 
[Dispatchers.setMain][setMain] then expose [TestCoroutineScope] for use in tests.

### Providing an explicit `TestCoroutineDispatcher`

While providing a [TestCoroutineScope] is slightly preferred due to the improved uncaught exception handling, there are 
many situations where it is easier to provide a [TestCoroutineDispatcher]. For example [Dispatchers.setMain][setMain] 
does not accept a [TestCoroutineScope] and requires a [TestCoroutineDispatcher] to control coroutine execution in 
tests.

The main difference between `TestCoroutineScope` and `TestCoroutineDispatcher` is how uncaught exceptions are handled. 
When using `TestCoroutineDispatcher` uncaught exceptions thrown in coroutines will use regular 
[coroutine exception handling](https://kotlinlang.org/docs/reference/coroutines/exception-handling.html). 
`TestCoroutineScope` will always use `TestCoroutineDispatcher` as it's dispatcher.

A test can use a `TestCoroutineDispatcher` without declaring an explicit `TestCoroutineScope`. This is preferred 
when the class under test allows a test to provide a [CoroutineDispatcher] but does not allow the test to provide a 
[CoroutineScope].

Since [TestCoroutineDispatcher] is stateful in order to keep track of executing coroutines, it is 
important to ensure that [cleanupTestCoroutines][TestCoroutineDispatcher.cleanupTestCoroutines] is called after every test case. 

```kotlin
class TestClass {
    private val testDispatcher = TestCoroutineDispatcher()
        
    @Before
    fun setup() {
        // provide the scope explicitly, in this example using a constructor parameter
        Dispatchers.setMain(testDispatcher)
    }
    
    @After
    fun cleanUp() {
        Dispatchers.resetMain()
        testScope.cleanupTestCoroutines()
    }
    
    @Test
    fun testFoo() = testDispatcher.runBlockingTest {
        // TestCoroutineDispatcher.runBlockingTest uses `testDispatcher` to run coroutines 
        foo()
    }
}

fun foo() {
    MainScope().launch { 
        // launch will use the testDispatcher provided by setMain
    }
}
```

*Note:* Prefer to provide `TestCoroutineScope` when it does not complicate code since it will also elevate exceptions 
to test failures. However, exposing a `CoroutineScope` to callers of a function may lead to complicated code, in which 
case this is the preferred pattern.

### Using `TestCoroutineScope` and `TestCoroutineDispatcher` without `runBlockingTest`

It is supported to use both [TestCoroutineScope] and [TestCoroutineDispatcher] without using the [runBlockingTest] 
builder. Tests may need to do this in situations such as introducing multiple dispatchers and library writers may do 
this to provide alternatives to `runBlockingTest`.

```kotlin
@Test
fun testFooWithAutoProgress() {
    val scope = TestCoroutineScope()
    scope.foo()
    // foo is suspended waiting for time to progress
    scope.advanceUntilIdle()
    // foo's coroutine will be completed before here
}

fun CoroutineScope.foo() {
    launch {
        println(1)            // executes eagerly when foo() is called due to TestCoroutineScope
        delay(1_000)          // suspends until time is advanced by at least 1_000
        println(2)            // executes after advanceTimeUntilIdle
    }
} 
```

## Using time control with `withContext`

Calls to `withContext(Dispatchers.IO)` or `withContext(Dispatchers.Default)` are common in coroutines based codebases. 
Both dispatchers are not designed to interact with `TestCoroutineDispatcher`.

Tests should provide a `TestCoroutineDispatcher` to replace these dispatchers if the `withContext` calls `delay` in the
function under test. For example, a test that calls `veryExpensiveOne` should provide a `TestCoroutineDispatcher` using
either dependency injection, a service locator, or a default parameter. 

```kotlin
suspend fun veryExpensiveOne() = withContext(Dispatchers.Default) {
    delay(1_000)
    1 // for very expensive values of 1
}
```

In situations where the code inside the `withContext` is very simple, it is not as important to provide a test 
dispatcher. The function `veryExpensiveTwo` will behave identically in a `TestCoroutineDispatcher` and 
`Dispatchers.Default` after the thread switch for `Dispatchers.Default`. Because `withContext` always returns a value by
directly, there is no need to inject a `TestCoroutineDispatcher` into this function.

```kotlin
suspend fun veryExpensiveTwo() = withContext(Dispatchers.Default) {
    2 // for very expensive values of 2
}
```

Tests should provide a `TestCoroutineDispatcher` to code that calls `withContext` to provide time control for 
delays, or when execution control is needed to test complex logic.


### Status of the API

This API is experimental and it is may change before migrating out of experimental (while it is marked as
[`@ExperimentalCoroutinesApi`][ExperimentalCoroutinesApi]).
Changes during experimental may have deprecation applied when possible, but it is not
advised to use the API in stable code before it leaves experimental due to possible breaking changes.

If you have any suggestions for improvements to this experimental API please share them them on the 
[issue tracker](https://github.com/Kotlin/kotlinx.coroutines/issues).

<!--- MODULE kotlinx-coroutines-core -->
<!--- INDEX kotlinx.coroutines -->
[Dispatchers.Main]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-dispatchers/-main.html
[CoroutineDispatcher]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-coroutine-dispatcher/index.html
[launch]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/launch.html
[async]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/async.html
[delay]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/delay.html
[CoroutineScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-coroutine-scope/index.html
[ExperimentalCoroutinesApi]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-experimental-coroutines-api/index.html
<!--- MODULE kotlinx-coroutines-test -->
<!--- INDEX kotlinx.coroutines.test -->
[setMain]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-test/kotlinx.coroutines.test/kotlinx.coroutines.-dispatchers/set-main.html
[runBlockingTest]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-test/kotlinx.coroutines.test/run-blocking-test.html
[UncompletedCoroutinesError]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-test/kotlinx.coroutines.test/-uncompleted-coroutines-error/index.html
[DelayController]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-test/kotlinx.coroutines.test/-delay-controller/index.html
[DelayController.advanceUntilIdle]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-test/kotlinx.coroutines.test/-delay-controller/advance-until-idle.html
[DelayController.pauseDispatcher]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-test/kotlinx.coroutines.test/-delay-controller/pause-dispatcher.html
[TestCoroutineDispatcher]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-test/kotlinx.coroutines.test/-test-coroutine-dispatcher/index.html
[DelayController.resumeDispatcher]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-test/kotlinx.coroutines.test/-delay-controller/resume-dispatcher.html
[TestCoroutineScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-test/kotlinx.coroutines.test/-test-coroutine-scope/index.html
[TestCoroutineExceptionHandler]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-test/kotlinx.coroutines.test/-test-coroutine-exception-handler/index.html
[TestCoroutineScope.cleanupTestCoroutines]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-test/kotlinx.coroutines.test/-test-coroutine-scope/cleanup-test-coroutines.html
<!--- END -->
