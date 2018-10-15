package kotlinx.coroutines.experimental.androidx.lifecycle

import androidx.annotation.Keep
import kotlinx.coroutines.experimental.MainCoroutineDispatcher
import kotlinx.coroutines.experimental.Runnable
import kotlinx.coroutines.experimental.internal.MainDispatcherFactory
import kotlinx.coroutines.experimental.newSingleThreadContext
import kotlin.coroutines.experimental.CoroutineContext

public class TestMainDispatcher : MainCoroutineDispatcher() {
    private val singleThreadDispatcher = newSingleThreadContext("test-main-dispatcher")
    override val immediate: MainCoroutineDispatcher
        get() = TODO("Should not be needed for current tests as of 2018/10/15")

    override fun dispatch(context: CoroutineContext, block: Runnable) {
        return singleThreadDispatcher.dispatch(context, block)
    }

    fun close() = default.singleThreadDispatcher.close()

    companion object {
        val default by lazy { TestMainDispatcher() }
    }
}


@Keep
internal class TestAndroidDispatcherFactory : MainDispatcherFactory {
    override fun createDispatcher(): MainCoroutineDispatcher = TestMainDispatcher.default
    override val loadPriority: Int get() = Int.MAX_VALUE
}
