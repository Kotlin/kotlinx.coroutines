package kotlinx.coroutines

import kotlinx.coroutines.future.*
import org.junit.Test
import kotlin.test.*

/*
 * Integration test that ensures signatures from both the jdk8 and the core source sets of the kotlinx-coroutines-core subproject are used.
 */
class Jdk8InCoreIntegration {

    @Test
    fun testFuture() = runBlocking<Unit> {
        val future = future { yield(); 42 }
        future.whenComplete { r, _ -> assertEquals(42, r)  }
        assertEquals(42, future.await())
    }
}
