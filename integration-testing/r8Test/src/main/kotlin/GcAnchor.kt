import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.flow.*
import java.lang.ref.WeakReference
import kotlin.coroutines.EmptyCoroutineContext
import kotlin.time.Duration.Companion.milliseconds
import kotlin.time.Duration.Companion.seconds

/**
 * Verifies that R8 doesn't strip the GC anchor (`job` field) from ReadonlyStateFlow.
 *
 * The test uses a callbackFlow where a separate coroutine emits values through a WeakReference.
 * If the sharing coroutine is collected by GC (because R8 removed the anchor), the callbackFlow
 * is cancelled, the weak reference is cleared, and emissions stop.
 */
val shared = callbackFlow {
    val emitter = Runnable { trySend(Unit) }
    val weak = WeakReference(emitter)
    CoroutineScope(EmptyCoroutineContext).launch {
        while (true) {
            weak.get()?.run() ?: break
            delay(1.seconds)
        }
    }
    awaitClose { emitter.run() } // strong ref to emitter prevents GC before close
}.runningFold(0) { count, _ ->
    count + 1
}.stateIn(
    scope = CoroutineScope(EmptyCoroutineContext),
    started = SharingStarted.Eagerly,
    initialValue = 0
)

fun main(): Unit = runBlocking {
    delay(100.milliseconds)
    repeat(5) {
        System.gc()
        delay(1.seconds)
    }
    val lastValue = shared.value
    check(lastValue >= 5) {
        "Expected the sharing coroutine to survive GC (at least 5 emissions), but the last emitted value was $lastValue"
    }
}
