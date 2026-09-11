package kotlinx.coroutines

import kotlin.coroutines.CoroutineContext
import kotlinx.coroutines.testing.*
import kotlin.test.*

class MainCoroutineDispatcherTest: TestBase() {
    @Test
    fun testToStringNotFailingIfMainDispatcherIsMissing() {
        val myDispatcher = object: MainCoroutineDispatcher() {
            override val immediate get() = TODO()

            override fun dispatch(context: CoroutineContext, block: Runnable) {
                TODO()
            }
        }
        myDispatcher.toString()
    }
}
