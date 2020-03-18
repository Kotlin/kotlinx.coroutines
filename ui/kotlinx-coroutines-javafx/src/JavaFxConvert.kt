/*
 *  Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.javafx

import javafx.beans.value.ChangeListener
import javafx.beans.value.ObservableValue
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.awaitClose
import kotlinx.coroutines.flow.*

/**
 * Creates an instance of a cold [Flow] that subscribes to the given [ObservableValue] and emits
 * its values as they change. The resulting flow is conflated, meaning that if several values arrive in quick
 * succession, only the last one will be emitted.
 * Since this implementation uses [ObservableValue.addListener], even if this [ObservableValue]
 * supports lazy evaluation, eager computation will be enforced while the flow is being collected.
 * All the calls to JavaFX API are performed in [Dispatchers.JavaFx].
 * This flow emits at least the initial value.
 *
 * ### Operator fusion
 *
 * Adjacent applications of [flowOn], [buffer], [conflate], and [produceIn] to the result of `asFlow` are fused.
 * [conflate] has no effect, as this flow is already conflated; one can use [buffer] to change that instead.
 */
@ExperimentalCoroutinesApi
public fun <T> ObservableValue<T>.asFlow(): Flow<T> = callbackFlow<T> {
    val listener = ChangeListener<T> { _, _, newValue ->
        try {
            offer(newValue)
        } catch (e: CancellationException) {
            // In case the event fires after the channel is closed
        }
    }
    addListener(listener)
    send(value)
    awaitClose {
        removeListener(listener)
    }
}.flowOn(Dispatchers.JavaFx).conflate()
