package kotlinx.coroutines.test.internal

import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*

internal class TestMainDispatcherFactory : MainDispatcherFactory {

    override fun createDispatcher(allFactories: List<MainDispatcherFactory>): MainCoroutineDispatcher {
        val otherFactories = allFactories.filter { it !== this }
        val secondBestFactory = otherFactories.maxByOrNull { it.loadPriority } ?: MissingMainCoroutineDispatcherFactory
        /* Do not immediately create the alternative dispatcher, as with `SUPPORT_MISSING` set to `false`,
        it will throw an exception. Instead, create it lazily. */
        return TestMainDispatcher({
            val dispatcher = try {
                secondBestFactory.tryCreateDispatcher(otherFactories)
            } catch (e: Throwable) {
                reportMissingMainCoroutineDispatcher(e)
            }
            if (dispatcher.isMissing()) {
                reportMissingMainCoroutineDispatcher(runCatching {
                    // attempt to dispatch something to the missing dispatcher to trigger the exception.
                    dispatcher.dispatch(dispatcher, Runnable { })
                }.exceptionOrNull()) // can not be null, but it does not matter.
            } else {
                dispatcher
            }
        })
    }

    /**
     * [Int.MAX_VALUE] -- test dispatcher always wins no matter what factories are present in the classpath.
     * By default, all actions are delegated to the second-priority dispatcher, so that it won't be the issue.
     */
    override val loadPriority: Int
        get() = Int.MAX_VALUE
}

internal actual fun Dispatchers.getTestMainDispatcher(): TestMainDispatcher {
    val mainDispatcher = Main
    require(mainDispatcher is TestMainDispatcher) { "TestMainDispatcher is not set as main dispatcher, have $mainDispatcher instead." }
    return mainDispatcher
}

private fun reportMissingMainCoroutineDispatcher(e: Throwable? = null): Nothing {
    throw IllegalStateException(
        "Dispatchers.Main was accessed when the platform dispatcher was absent " +
            "and the test dispatcher was unset. Please make sure that Dispatchers.setMain() is called " +
            "before accessing Dispatchers.Main and that Dispatchers.Main is not accessed after " +
            "Dispatchers.resetMain().",
        e
    )
}
