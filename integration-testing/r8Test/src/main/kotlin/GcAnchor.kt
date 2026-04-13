import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.flow.*
import java.lang.ref.WeakReference
import kotlin.coroutines.ContinuationInterceptor

/**
 * Verifies that R8 doesn't strip the GC anchor (`job` field) from ReadonlyStateFlow.
 *
 * If the sharing coroutine is collected by GC (because R8 removed the anchor),
 * the channelFlow coroutine gets dropped, together with the WeakReference.
 */
@OptIn(DelicateCoroutinesApi::class)
fun main(): Unit = runBlocking {
    val latch = Channel<Unit>(1)
    lateinit var weak: WeakReference<() -> Unit>
    val shared = channelFlow {
        val emitter: () -> Unit = { trySend(Unit) }
        weak = WeakReference(emitter)
        latch.trySend(Unit)
        awaitClose { emitter() } // strong ref to emitter prevents GC before close
    }.stateIn(
        scope = GlobalScope + currentCoroutineContext()[ContinuationInterceptor]!!,
        started = SharingStarted.Eagerly,
        initialValue = Unit
    )
    latch.receive() // the weak reference got initialized by this point
    System.gc()
    check(weak.get() != null) { "The weak reference got collected but shouldn't have been." }
    shared.value // a strong reference to `shared`
}
