package kotlinx.coroutines.test.internal

import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*

internal class TestMainDispatcherFactory : MainDispatcherFactory {

    override fun createDispatcher(allFactories: List<MainDispatcherFactory>): MainCoroutineDispatcher {
        val otherFactories = allFactories.filter { it !== this }
        val secondBestFactory = otherFactories.maxByOrNull { it.loadPriority } ?: MissingMainCoroutineDispatcherFactory
        /* Do not immediately create the alternative dispatcher, as with `SUPPORT_MISSING` set to `false`,
        it will throw an exception. Instead, create it lazily. */
        return TestMainDispatcher({ secondBestFactory.tryCreateDispatcher(otherFactories) })
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
