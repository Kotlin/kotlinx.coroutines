package kotlinx.coroutines.androidx.lifecycle

import androidx.annotation.Keep
import kotlinx.coroutines.MainCoroutineDispatcher
import kotlinx.coroutines.Runnable
import kotlinx.coroutines.internal.MainDispatcherFactory
import kotlinx.coroutines.newSingleThreadContext
import kotlin.coroutines.CoroutineContext

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
