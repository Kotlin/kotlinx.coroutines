package kotlinx.coroutines.test.internal
import kotlinx.coroutines.*

@Suppress("INVISIBLE_MEMBER", "INVISIBLE_REFERENCE")
internal actual fun Dispatchers.getTestMainDispatcher(): TestMainDispatcher =
    when (val mainDispatcher = Main) {
        is TestMainDispatcher -> mainDispatcher
        else -> TestMainDispatcher(mainDispatcher).also { injectMain(it) }
    }