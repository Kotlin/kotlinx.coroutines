package kotlinx.coroutines.debug.junit5

import kotlinx.coroutines.*
import org.junit.jupiter.api.*

/**
 * Tests usage of [CoroutinesTimeout] on classes and test methods when only methods are annotated.
 *
 * This test class is not intended to be run manually. Instead, use [CoroutinesTimeoutTest] as the entry point.
 */
@TestMethodOrder(MethodOrderer.OrderAnnotation::class)
class CoroutinesTimeoutMethodTest {

    @Test
    @Order(1)
    fun noClassTimeout() {
        runBlocking {
            delay(150)
        }
    }

    @CoroutinesTimeout(100)
    @Test
    @Order(2)
    fun usesMethodTimeoutWithNoClassTimeout() {
        runBlocking {
            delay(1000)
        }
    }

    @CoroutinesTimeout(1000)
    @Test
    @Order(3)
    fun fitsInMethodTimeout() {
        runBlocking {
            delay(10)
        }
    }

}
