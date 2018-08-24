package kotlinx.coroutines.experimental.firebase.android

import com.google.firebase.database.DataSnapshot
import com.google.firebase.database.DatabaseError
import com.google.firebase.database.Query
import com.google.firebase.database.ValueEventListener
import kotlinx.coroutines.experimental.suspendCancellableCoroutine

private suspend fun <T : Any> awaitQuerySingleValue(query: Query, type: Class<T>): T =
        suspendCancellableCoroutine { continuation ->
            val listener = object : ValueEventListener {
                override fun onDataChange(snapshot: DataSnapshot) = try {
                    continuation.resume(snapshot.getValue(type)!!)
                } catch (exception: Exception) {
                    continuation.resumeWithException(exception)
                }

                override fun onCancelled(error: DatabaseError) =
                        continuation.resumeWithException(error.toException())
            }

            query.addListenerForSingleValueEvent(listener)
            continuation.invokeOnCompletion { query.removeEventListener(listener) }
        }

public suspend fun <T : Any> Query.readValue(type: Class<T>): T = awaitQuerySingleValue(this, type)

public suspend inline fun <reified T : Any> Query.readValue(): T = readValue(T::class.java)

private suspend fun <T : Any> awaitQueryListValue(query: Query, type: Class<T>): List<T> =
        suspendCancellableCoroutine { continuation ->
            val listener = object : ValueEventListener {
                override fun onDataChange(snapshot: DataSnapshot) = try {
                    val data: List<T> = snapshot.children.toHashSet().map { it.getValue(type)!! }

                    continuation.resume(data)
                } catch (exception: Exception) {
                    continuation.resumeWithException(exception)
                }

                override fun onCancelled(error: DatabaseError) =
                        continuation.resumeWithException(error.toException())
            }

            query.addListenerForSingleValueEvent(listener)
            continuation.invokeOnCompletion { query.removeEventListener(listener) }
        }

public suspend fun <T : Any> Query.readList(type: Class<T>): List<T> = awaitQueryListValue(this, type)

public suspend inline fun <reified T : Any> Query.readList(): List<T> = readList(T::class.java)
