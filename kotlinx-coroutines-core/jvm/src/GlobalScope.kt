package kotlinx.coroutines

import kotlinx.coroutines.internal.loadServices
import kotlin.coroutines.CoroutineContext
import kotlin.coroutines.EmptyCoroutineContext

internal actual fun createInitialContext(): CoroutineContext {
    // Combine context elements provided by libraries
    return loadServices<InitialContextProvider>()
        .fold(EmptyCoroutineContext) { acc: CoroutineContext, provider -> acc + provider.element }
}

interface InitialContextProvider {

    val element: CoroutineContext.Element

}
