# Module kotlinx-coroutines-test-js

Core utilities to use for testing coroutines on Kotlin/JS.

```kotlin
class CoroutinesTest : TestBase() {
    @Test
    fun testLaunchAndYieldJoin() = runTest {
        expect(1)
        val job = launch(coroutineContext) {
            expect(3)
            yield()
            expect(4)
        }
        expect(2)
        assertTrue(job.isActive && !job.isCompleted)
        job.join()
        assertTrue(!job.isActive && job.isCompleted)
        finish(5)
    }
}
```