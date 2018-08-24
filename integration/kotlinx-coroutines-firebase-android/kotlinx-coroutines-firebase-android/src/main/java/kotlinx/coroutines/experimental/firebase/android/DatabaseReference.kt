package kotlinx.coroutines.experimental.firebase.android

import com.google.firebase.FirebaseException
import com.google.firebase.database.DataSnapshot
import com.google.firebase.database.DatabaseError
import com.google.firebase.database.DatabaseReference
import com.google.firebase.database.GenericTypeIndicator
import com.google.firebase.database.Query
import com.google.firebase.database.ValueEventListener
import kotlinx.coroutines.experimental.suspendCancellableCoroutine

/**
 * Coroutine to read a single value from Firebase Database
 *
 * This method is not intended to be used in the code. It's just a base function that contains the
 * main coroutine code that reads a single value from Firebase Database. To use it's functionality
 * call [kotlinx.coroutines.experimental.firebase.android.readValue] function.
 *
 * The implementation consists of a [suspendCancellableCoroutine] that encapsulates a
 * [ValueEventListener].
 *
 * @param reference The Firebase Database node to be read.
 * @param type Expected type wrapped in a Class instance.
 * @param T The type of the expected value from Firebase Database.
 * @return The persisted object of the type T informed.
 */
private suspend fun <T : Any> readReference(
        reference: DatabaseReference,
        type: Class<T>
): T = suspendCancellableCoroutine { continuation ->
    val listener = object : ValueEventListener {

        /**
         * Callback to handle Firebase Database errors
         *
         * It's triggered when there are authentication problems or network error. To see all
         * possible, pleese refer to Firebase Database docs.
         *
         * @link https://firebase.google.com/docs/reference/android/com/google/firebase/database/DatabaseError
         * @param error The error occurred.
         * @throws FirebaseException When the error happens within Firebase SDK.
         */
        override fun onCancelled(error: DatabaseError) =
                continuation.resumeWithException(error.toException())

        /**
         * Callback to handle Firebase Database queries
         *
         * It's triggered when the requested value is available to access.
         *
         * @link https://firebase.google.com/docs/reference/android/com/google/firebase/database/DataSnapshot
         * @param snapshot The data retrieved.
         * @throws Exception The data retrieved could not be converted to the type informed.
         */
        override fun onDataChange(snapshot: DataSnapshot) {
            try {
                val data: T? = snapshot.getValue(type)

                continuation.resume(data!!)
            } catch (exception: Exception) {
                continuation.resumeWithException(exception)
            }
        }
    }

    continuation.invokeOnCompletion { reference.removeEventListener(listener) }

    reference.addListenerForSingleValueEvent(listener)
}

/**
 * Coroutine to read a single value from Firebase Database
 *
 * Example:
 * ```kotlin
 * val message = FirebaseDatabase.getInstance()
 *     .getReference("message")
 *     .readValue(String::class.java)
 *
 * println(message) // Hello World
 * ```
 *
 * @param type Expected type wrapped in a Class instance.
 * @param T The type of the expected value from Firebase Database.
 * @return The persisted object of the type T informed.
 */
public suspend fun <T : Any> DatabaseReference.readValue(type: Class<T>): T = readReference(this, type)

/**
 * Coroutine to read a single value from Firebase Database
 *
 * ```kotlin
 * val message = FirebaseDatabase.getInstance()
 *     .getReference("message")
 *     .readValue<String>()
 *
 * println(message) // Hello World
 * ```
 *
 * @param T The type of the expected value from Firebase Database.
 * @return The persisted object of the type T informed.
 */
public suspend inline fun <reified T : Any> DatabaseReference.readValue(): T = readValue(T::class.java)

/**
 * Coroutine to read a collection of values from Firebase Database
 *
 * This method is not intended to be used in the code. It's just a base function that contains the
 * main coroutine code that reads a collection of values from Firebase Database. To use it's
 * functionality call [kotlinx.coroutines.experimental.firebase.android.readValue] function.
 *
 * The implementation consists of a [suspendCancellableCoroutine] that encapsulates a
 * [ValueEventListener].
 *
 * @param reference The Firebase Database node to be read.
 * @param type Expected type wrapped in a Class instance.
 * @param T The type of the expected value from Firebase Database.
 * @return The persisted object of the type T informed.
 */
private suspend fun <T : Any> readReferences(
        reference: DatabaseReference,
        type: Class<T>
): List<T> = suspendCancellableCoroutine { continuation ->
    val listener = object : ValueEventListener {

        /**
         * Callback to handle Firebase Database errors
         *
         * It's triggered when there are authentication problems or network error. To see all
         * possible, pleese refer to Firebase Database docs.
         *
         * @link https://firebase.google.com/docs/reference/android/com/google/firebase/database/DatabaseError
         * @param error The error occurred.
         * @throws FirebaseException When the error happens within Firebase SDK.
         */
        override fun onCancelled(error: DatabaseError) =
                continuation.resumeWithException(error.toException())

        /**
         * Callback to handle Firebase Database queries
         *
         * It's triggered when the requested value is available to access.
         *
         * @link https://firebase.google.com/docs/reference/android/com/google/firebase/database/DataSnapshot
         * @param snapshot The data retrieved.
         * @throws Exception The data retrieved could not be converted to the type informed.
         */
        override fun onDataChange(snapshot: DataSnapshot) {
            try {
                val data: List<T> = snapshot.children.toHashSet().map { it.getValue(type)!! }

                continuation.resume(data)
            } catch (exception: Exception) {
                continuation.resumeWithException(exception)
            }
        }
    }

    continuation.invokeOnCompletion { reference.removeEventListener(listener) }

    reference.addListenerForSingleValueEvent(listener)
}

/**
 * Coroutine to read a list of values from Firebase Database
 *
 * This method returns an implementation of [List] interface with the generic type informed. It's
 * different from [kotlinx.coroutines.experimental.firebase.android.readValue] function because of
 * the way that Firebase serialize and deserialize values.
 *
 * Example:
 * ```kotlin
 * val names = FirebaseDatabase.getInstance()
 *     .getReference("names")
 *     .readList(String::class.java)
 *
 * names.forEach(::println) // ["Adam", "Monica"]
 * ```
 *
 * @param type Expected type wrapped in a Class instance.
 * @param T The type of the expected value from Firebase Database.
 * @return The persisted object of the type T informed.
 */
public suspend fun <T : Any> DatabaseReference.readList(type: Class<T>): List<T> = readReferences(this, type)

/**
 * Coroutine to read a list of values from Firebase Database
 *
 * This method returns an implementation of [List] interface with the generic type informed. It's
 * different from [kotlinx.coroutines.experimental.firebase.android.readValue] function because of
 * the way that Firebase serialize and deserialize values.
 *
 * Example:
 * ```kotlin
 * val names = FirebaseDatabase.getInstance()
 *     .getReference("names")
 *     .readList<String>()
 *
 * names.forEach(::println) // ["Adam", "Monica"]
 * ```
 *
 * @param T The type of the expected value from Firebase Database.
 * @return The persisted object of the type T informed.
 */
suspend inline fun <reified T : Any> DatabaseReference.readList(): List<T> = readList(T::class.java)

public suspend fun <T : Any> DatabaseReference.saveValue(value: T): Unit =
        setValue(value).await().let { kotlin.Unit }

public suspend fun <T : Any> DatabaseReference.pushValue(value: T): Unit = push().saveValue(value)

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
