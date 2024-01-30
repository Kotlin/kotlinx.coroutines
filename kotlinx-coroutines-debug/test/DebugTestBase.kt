package kotlinx.coroutines.debug


import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlinx.coroutines.debug.junit4.*
import org.junit.*

open class DebugTestBase : TestBase() {

    @JvmField
    @Rule
    val timeout = CoroutinesTimeout.seconds(60)

    @Before
    open fun setUp() {
        before()
        DebugProbes.sanitizeStackTraces = false
        DebugProbes.enableCreationStackTraces = false
        DebugProbes.install()
    }

    @After
    fun tearDown() {
        try {
            DebugProbes.uninstall()
        } finally {
            onCompletion()
        }
    }
}
