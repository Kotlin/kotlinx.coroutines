package kotlinx.coroutines.test.internal

import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*

internal class TestMainDispatcherFactory : MainDispatcherFactory {

    override fun createDispatcher(allFactories: List<MainDispatcherFactory>): MainCoroutineDispatcher =
        TestMainDispatcher(createInnerMain = {
            /* Trying to allocate a non-test `Dispatchers.Main` may fail:
               for example, `kotlinx-coroutines-android`'s implementation requires the Android runtime.
               So, we won't even attempt to construct the alternative dispatcher until it's necessary. */
            try {
                val otherFactories = allFactories.filter { it !== this }
                val secondBestFactory = otherFactories.maxByOrNull { it.loadPriority }
                secondBestFactory?.createDispatcher(otherFactories)
            } catch (e: Throwable) {
                /** Ignoring [MainDispatcherFactory.hintOnError] because the only implementation right now suggests
                 * using `kotlinx-coroutines-test`, so the hint is useless in this scenario. */
                reportMissingMainCoroutineDispatcher(e)
            } ?: reportMissingMainCoroutineDispatcher()
        })

    /**
     * [Int.MAX_VALUE] -- test dispatcher always wins no matter what factories are present in the classpath.
     * By default, all actions are delegated to the second-priority dispatcher, so that it won't be the issue.
     */
    override val loadPriority: Int
        get() = Int.MAX_VALUE
}

internal actual fun Dispatchers.getOrInstallTestMainDispatcher(): TestMainDispatcher {
    val mainDispatcher = try {
        Main
    } catch (e: IllegalStateException) {
        /**
         * This can happen if [Main] is some other Main dispatcher with a higher priority
         * or if the [TestMainDispatcherFactory] wasn't discovered by [java.util.ServiceLoader].
         * We do not have any first-party Main dispatchers with a higher priority than the test one,
         * and we do not support them, so this exception assumes the second scenario.
         */
        throw IllegalStateException(
            "Failed to install a `kotlinx.coroutines.test` Main dispatcher as Dispatchers.Main", e
        )
    }
    check(mainDispatcher is TestMainDispatcher) { "TestMainDispatcher is not set as main dispatcher, have $mainDispatcher instead." }
    return mainDispatcher
}

internal actual fun Dispatchers.getTestMainDispatcherOrNull(): TestMainDispatcher? = try {
    Main as? TestMainDispatcher
} catch (_: IllegalStateException) {
    /**
     * This may happen in one case only: [TestMainDispatcher] was not successfully installed as the Main dispatcher.
     * Then, the current Main dispatcher isn't a [TestMainDispatcher], so we have to return `null`.
     */
    null
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
