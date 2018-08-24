package kotlinx.coroutines.experimental.firebase.android

import com.google.android.gms.tasks.OnCanceledListener
import com.google.android.gms.tasks.OnFailureListener
import com.google.android.gms.tasks.OnSuccessListener
import com.google.android.gms.tasks.Task
import kotlinx.coroutines.experimental.cancel
import kotlinx.coroutines.experimental.suspendCancellableCoroutine
import kotlin.coroutines.experimental.Continuation
import java.lang.Exception

/**
 * Coroutine support to Firebase Task interface
 *
 * This extension function allows you to interact with a Firebase [com.google.android.gms.tasks.Task]
 * using the `await()` method instead of the standard listeners.
 *
 * There is a sample code below comparing the two approaches. Assuming that
 * `auth` variable has the value returned from `FirebaseAuth.getInstance()`
 * method call then your code can be something like:
 *
 * ```
 * auth.getUserByEmail(email)
 *   .addOnSuccessListener { user -> println(user) }
 *   .addOnFailureListener { exception -> println(exception) }
 * ```
 *
 * When using the coroutine approach, it should be more like this:
 *
 * ```
 * try {
 *     val user = auth.getUserByEmail(email).await()
 *     println(user)
 * } catch (exception: Exception) {
 *     println(exception)
 * }
 * ```
 *
 * @param T The type of the value been returned
 * @throws Exception Thrown in case of network error or other reasons described in the Firebase docs
 * @return The value returned by the Firebase success callback
 */
suspend fun <T> Task<T>.await(): T = suspendCancellableCoroutine { continuation ->
    val consumer = FirebaseCallbackConsumer(continuation)

    this
            .addOnSuccessListener { consumer.onSuccess(it) }
            .addOnFailureListener { consumer.onFailure(it) }
            .addOnCanceledListener{ consumer.onCanceled() }
}

private class FirebaseCallbackConsumer<T>(
        val continuation: Continuation<T>
) : OnSuccessListener<T>, OnFailureListener, OnCanceledListener {

    override fun onSuccess(result: T) = continuation.resume(result)

    override fun onFailure(exception: Exception) = continuation.resumeWithException(exception)

    override fun onCanceled() {
        continuation.context.cancel()
    }
}
