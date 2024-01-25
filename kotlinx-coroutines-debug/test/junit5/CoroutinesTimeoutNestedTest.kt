package kotlinx.coroutines.debug.junit5

import kotlinx.coroutines.*
import org.junit.jupiter.api.*

/**
 * This test checks that nested classes correctly recognize the [CoroutinesTimeout] annotation.
 *
 * This test class is not intended to be run manually. Instead, use [CoroutinesTimeoutTest] as the entry point.
 */
@CoroutinesTimeout(200)
class CoroutinesTimeoutNestedTest {
    @Nested
    inner class NestedInInherited {
        @Test
        fun usesOuterClassTimeout() = runBlocking {
            delay(1000)
        }

        @Test
        fun fitsInOuterClassTimeout() = runBlocking {
            delay(10)
        }
    }
}
