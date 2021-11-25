/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

/**
 * [FlowCollector] is used as an intermediate or a terminal collector of the flow and represents
 * an entity that accepts values emitted by the [Flow].
 *
 * This interface should usually not be implemented directly, but rather used as a receiver in a [flow] builder when implementing a custom operator,
 * or with SAM-conversion.
 * Implementations of this interface are not thread-safe.
 *
 * Example of usage:
 *
 * ```
 * val flow = getMyEvents()
 * try {
 *     flow.collect { value ->
 *         println("Received $value")
 *     }
 *     println("My events are consumed successfully")
 * } catch (e: Throwable) {
 *     println("Exception from the flow: $e")
 * }
 * ```
 */
public fun interface FlowCollector<in T> {

    /**
     * Collects the value emitted by the upstream.
     * This method is not thread-safe and should not be invoked concurrently.
     */
    public suspend fun emit(value: T)
}
