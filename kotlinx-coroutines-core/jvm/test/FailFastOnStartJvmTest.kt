@file:Suppress("DeferredResultUnused")

package kotlinx.coroutines

import kotlinx.coroutines.channels.*
import kotlinx.coroutines.testing.*
import org.junit.*
import org.junit.Test
import org.junit.rules.*
import kotlin.test.*

class FailFastOnStartJvmTest : TestBase() {

    @Rule
    @JvmField
    val timeout: Timeout = Timeout.seconds(5)

    @Test
    fun testActor() = runTest(expected = ::mainException) {
        actor<Int>(Dispatchers.Main) { fail() }
    }

    @Test
    fun testActorLazy() = runTest(expected = ::mainException) {
        val actor = actor<Int>(Dispatchers.Main, start = CoroutineStart.LAZY) { fail() }
        actor.send(1)
    }

    private fun mainException(e: Throwable): Boolean {
        return e is IllegalStateException && e.message?.contains("Module with the Main dispatcher is missing") ?: false
    }

}
