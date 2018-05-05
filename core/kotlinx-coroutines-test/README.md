# Module kotlinx-coroutines-test

Core utilities to use for testing coroutines.

```kotlin
class WithContextCommonPoolTest : TestBase() {
    @Test
    fun testCommonPoolNoSuspend() = runTest {
        expect(1)
        val result = withContext(CommonPool) {
            expect(2)
            "OK"
        }
        assertEquals("OK", result)
        finish(3)
    }
}
```