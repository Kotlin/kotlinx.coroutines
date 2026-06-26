package kotlinx.coroutines.test.internal
import kotlinx.coroutines.*

@Suppress("INVISIBLE_MEMBER", "INVISIBLE_REFERENCE") // do not remove the INVISIBLE_REFERENCE suppression: required in K2
internal actual fun Dispatchers.getOrInstallTestMainDispatcher(): TestMainDispatcher =
    when (val mainDispatcher = mainDispatcherOrNull()) {
        is TestMainDispatcher -> mainDispatcher
        null -> TestMainDispatcher(createInnerMain = {
            // Duplicates the fallback from the `Dispatchers.Main` implementation on Native.
            // Probably not yet worth introducing a new API for a clearer separation of concerns at this point.
            error("Dispatchers.Main is not supported on this platform")
        }).also { injectMain(it) }
        else -> TestMainDispatcher(mainDispatcher).also { injectMain(it) }
    }

@Suppress("INVISIBLE_MEMBER", "INVISIBLE_REFERENCE") // do not remove the INVISIBLE_REFERENCE suppression: required in K2
internal actual fun Dispatchers.getTestMainDispatcherOrNull(): TestMainDispatcher? =
    mainDispatcherOrNull() as? TestMainDispatcher
