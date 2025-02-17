package kotlinx.coroutines

import kotlin.test.Test

class AaaaaTest {
    @Test
    fun reproducer() = runBlocking(Dispatchers.Unconfined) {  }
}
