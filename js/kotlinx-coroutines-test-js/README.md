# Module kotlinx-coroutines-test-js

Core utilities to use for testing coroutines on Kotlin/JS.

Provides TestBase class for tests, so that tests for predictable scheduling of actions in multiple coroutines can be written. 

Use it like this:
```kotlin
class CoroutinesTest : TestBase() {
    @Test
    fun testLaunchAndYieldJoin() = runTest { // run in the test context, with Exception handling
        expect(1) // first step : initiate action counter
        val job = launch(coroutineContext) { // use the test context
            expect(3) // the body of this coroutine in going to be executed in the 3rd step
            yield() // yield launched job to test
            expect(4) // fourth step
        }
        expect(2) // launch just scheduled coroutine for exectuion later, so this line is executed second
        assertTrue(job.isActive && !job.isCompleted)
        job.join() // Suspends coroutine until launched job is complete
        assertTrue(!job.isActive && job.isCompleted)
        finish(5) // fifth step is the last one. `finish` must be invoked or test fails
    }
}
```