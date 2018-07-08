package kotlinx.coroutines.experimental.firebase.android

import com.google.android.gms.tasks.Task
import kotlinx.coroutines.experimental.suspendCancellableCoroutine
import kotlin.coroutines.experimental.suspendCoroutine

/**
 * Coroutine support to Firebase Task interface
 *
 * This method is not intended to be used in your code. You should probably use [await] sinsce it's
 * more idiomatic.
 *
 * The implementation is pretty simple. It justs use a [suspendCoroutine] to encapsulate the
 * Firebase [com.google.android.gms.tasks.OnCompleteListener] interface.
 *
 */
private suspend fun <T> awaitTask(task: Task<T>): T = suspendCancellableCoroutine { continuation ->
    task
            .addOnSuccessListener(continuation::resume)
            .addOnFailureListener(continuation::resumeWithException)
            .addOnCanceledListener { continuation.cancel() }
}

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
 *   val user = auth.getUserByEmail(email).await()
 *   println(user)
 * } catch (exception: Exception) {
 *   println(exception)
 * }
 * ```
 *
 * @param T The type of the value been returned
 * @throws Exception Thrown in case of network error or other reasons described in the Firebase docs
 * @return The value returned by the Firebase success callback
 */
suspend fun <T> Task<T>.await(): T = awaitTask(this)
