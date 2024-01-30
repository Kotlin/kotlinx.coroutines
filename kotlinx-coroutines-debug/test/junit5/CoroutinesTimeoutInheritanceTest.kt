package kotlinx.coroutines.debug.junit5

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import org.junit.jupiter.api.*

/**
 * Tests that [CoroutinesTimeout] is inherited.
 *
 * This test class is not intended to be run manually. Instead, use [CoroutinesTimeoutTest] as the entry point.
 */
class CoroutinesTimeoutInheritanceTest {

    @CoroutinesTimeout(100)
    open class Base

    @TestMethodOrder(MethodOrderer.OrderAnnotation::class)
    class InheritedWithNoTimeout: Base() {

        @Test
        @Order(1)
        fun usesBaseClassTimeout() = runBlocking {
            delay(1000)
        }

        @CoroutinesTimeout(300)
        @Test
        @Order(2)
        fun methodOverridesBaseClassTimeoutWithGreaterTimeout() = runBlocking {
            delay(200)
        }

        @CoroutinesTimeout(10)
        @Test
        @Order(3)
        fun methodOverridesBaseClassTimeoutWithLesserTimeout() = runBlocking {
            delay(50)
        }

    }

    @CoroutinesTimeout(300)
    class InheritedWithGreaterTimeout : TestBase() {

        @Test
        fun classOverridesBaseClassTimeout1() = runBlocking {
            delay(200)
        }

        @Test
        fun classOverridesBaseClassTimeout2() = runBlocking {
            delay(400)
        }

    }

}