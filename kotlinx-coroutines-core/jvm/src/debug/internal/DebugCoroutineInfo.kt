package kotlinx.coroutines.debug.internal

import kotlin.coroutines.*
import kotlin.coroutines.jvm.internal.*

/**
 * This class represents the data required by IDEA debugger.
 * IDEA debugger either directly reads data from the corresponding JVM fields of this class or calls the getters,
 * so we keep both for maximal flexibility for now.
 * **DO NOT MAKE BINARY-INCOMPATIBLE CHANGES TO THIS CLASS**.
 */
@Suppress("unused")
@PublishedApi
internal class DebugCoroutineInfo internal constructor(
    source: DebugCoroutineInfoImpl,
    public val context: CoroutineContext // field is used as of 1.4-M3
) {
    internal val creationStackBottom: CoroutineStackFrame? = source.creationStackBottom // field is used as of 1.4-M3
    public val sequenceNumber: Long = source.sequenceNumber // field is used as of 1.4-M3
    public val creationStackTrace = source.creationStackTrace // getter is used as of 1.4-M3
    public val state: String = source.state // getter is used as of 1.4-M3
    public val lastObservedThread: Thread? = source.lastObservedThread // field is used as of 1.4-M3
    public val lastObservedFrame: CoroutineStackFrame? = source.lastObservedFrame // field is used as of 1.4-M3
    @get:JvmName("lastObservedStackTrace") // method with this name is used as of 1.4-M3
    public val lastObservedStackTrace: List<StackTraceElement> = source.lastObservedStackTrace()
}
