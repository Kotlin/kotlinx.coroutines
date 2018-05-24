# Module kotlinx-coroutines-test

Core utilities to use for testing coroutines.

Provides [TestBase][kotlinx.coroutines.experimental.TestBase] class for tests, so that tests for predictable scheduling of actions in multiple coroutines sharing a single thread can be written. 

Use it like this:
```kotlin
class MyTest : TestBase() {
    @Test
    fun testSomething() = runTest { // run in the context of the main thread, with Exception handling
        expect(1) // first step : initiate action counter
        val job = launch(coroutineContext) { // use the context of the main thread
            expect(3) // the body of this coroutine in going to be executed in the 3rd step
        }
        expect(2) // launch just scheduled coroutine for exectuion later, so this line is executed second
        yield() // yield main thread to the launched job
        finish(4) // fourth step is the last one. `finish` must be invoked or test fails
    }
}
```

This module also provides a special CoroutineContext type [TestCoroutineCoroutineContext][kotlinx.coroutines.experimental.test.TestCoroutineContext] that
allows the writer of code that contains Coroutines with delays and timeouts to write non-flaky unit-tests for that code allowing these tests to
terminate in near zero time. See the documentation for this class for more information.

Use it like this:
```kotlin
class TestCoroutineContextTest {
    private val injectedContext = TestCoroutineContext()

    @After
    fun tearDown() {
        injectedContext.cancelAllActions()
    }
    
    @Test
    fun testDelayWithLaunch() = withTestContext(injectedContext) {
        val delay = 1000L
    
        var executed = false
        launch(this) {
            delay(delay)
            executed = true
        }
    
        advanceTimeBy(delay / 2)
        assertFalse(executed)
    
        advanceTimeBy(delay / 2)
        assertTrue(executed)
    }
}
```

<!--- MODULE kotlinx-coroutines-test -->
<!--- INDEX kotlinx.coroutines.experimental -->
[kotlinx.coroutines.experimental.TestBase]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-test/kotlinx.coroutines.experimental/-test-base/index.html
<!--- INDEX kotlinx.coroutines.experimental.test -->
[kotlinx.coroutines.experimental.test.TestCoroutineContext]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-test/kotlinx.coroutines.experimental.test/-test-coroutine-context/index.html
<!--- END -->
