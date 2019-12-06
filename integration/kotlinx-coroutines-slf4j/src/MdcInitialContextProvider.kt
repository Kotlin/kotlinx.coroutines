package kotlinx.coroutines.slf4j

import kotlinx.coroutines.InitialContextProvider
import kotlin.coroutines.CoroutineContext

class MdcInitialContextProvider : InitialContextProvider {
    override val element: CoroutineContext.Element
        get() = MDCContext(emptyMap())
}
