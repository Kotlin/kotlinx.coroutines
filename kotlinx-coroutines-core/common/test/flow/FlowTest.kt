@file:Suppress("PackageDirectoryMismatch")

package kotlinx.coroutines.flow

import kotlinx.coroutines.launch
import kotlinx.coroutines.testing.*
import kotlin.test.*

class FlowTest : TestBase() {
    @Test
    fun stateFlow() = runTest {
        val flow = MutableStateFlow(0)
        flow.compareAndSet(0, 42)
        flow.collect {
            println(it)
        }
    }

    @Test
    fun sharedFlow() = runTest {
        val flow = MutableSharedFlow<Int>(0)
        launch {
            flow.collect {
                println(it)
            }
        }
        flow.emit(42)
    }

    @Test
    fun channelFlow() = runTest {
        val flow = channelFlow { send(42) }
        flow.collect {
            println(it)
        }
    }
}
