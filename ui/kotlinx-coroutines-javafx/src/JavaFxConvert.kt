package kotlinx.coroutines.javafx

import javafx.beans.value.*
import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
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
@ExperimentalCoroutinesApi // Since 1.3.x
public fun <T> ObservableValue<T>.asFlow(): Flow<T> = callbackFlow<T> {
    val listener = ChangeListener<T> { _, _, newValue ->
        /*
         * Do not propagate the exception to the ObservableValue, it
         * already should've been handled by the downstream
         */
        trySend(newValue)
    }
    addListener(listener)
    send(value)
    awaitClose {
        removeListener(listener)
    }
}.flowOn(Dispatchers.JavaFx).conflate()
