package kotlinx.coroutines.android

import kotlinx.coroutines.*
import kotlin.coroutines.*

// Classes for testing service loader
internal class EmptyCoroutineScopeImpl1 : CoroutineScope {
    override val coroutineContext: CoroutineContext
        get() = EmptyCoroutineContext
}

internal class EmptyCoroutineScopeImpl2 : CoroutineScope {
    override val coroutineContext: CoroutineContext
        get() = EmptyCoroutineContext
}

internal class EmptyCoroutineScopeImpl3 : CoroutineScope {
    override val coroutineContext: CoroutineContext
        get() = EmptyCoroutineContext
}
