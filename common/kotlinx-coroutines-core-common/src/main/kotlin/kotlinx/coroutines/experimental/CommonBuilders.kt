package kotlinx.coroutines.experimental

import kotlin.coroutines.experimental.CoroutineContext
import kotlin.coroutines.experimental.EmptyCoroutineContext

@Suppress("EXPECTED_DECLARATION_WITH_DEFAULT_PARAMETER")
public expect fun launch(
    context: CoroutineContext = DefaultDispatcher,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    parent: Job? = null,
    block: suspend CoroutineScope.() -> Unit
): Job

@Suppress("EXPECTED_DECLARATION_WITH_DEFAULT_PARAMETER")
public expect suspend fun <T> withContext(
    context: CoroutineContext,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    block: suspend () -> T
): T

@Suppress("EXPECTED_DECLARATION_WITH_DEFAULT_PARAMETER")
public expect fun <T> runBlocking(
    context: CoroutineContext = EmptyCoroutineContext,
    block: suspend CoroutineScope.() -> T): T