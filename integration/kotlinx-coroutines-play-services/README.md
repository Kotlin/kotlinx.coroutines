# Module kotlinx-coroutines-play-services

Integration with Google Play Services [Tasks API](https://developers.google.com/android/guides/tasks).

Extension functions:

| **Name** | **Description**
| -------- | ---------------
| [Task.await][await] | Awaits for completion of the Task (cancellable)
| [Deferred.asTask][asTask] | Converts a deferred value to a Task

## Setup

_build.gradle_ (App module)

`implementation "org.jetbrains.kotlinx:kotlinx-coroutines-play-services:X.X.X"`

_See release versions: [Maven Repository]_


## Example

Using Firebase APIs becomes simple:

```kotlin
FirebaseAuth.getInstance().signInAnonymously().await()
val snapshot = try {
    FirebaseFirestore.getInstance().document("users/$id").get().await() // Cancellable await
} catch (e: FirebaseFirestoreException) {
    // Handle exception
    return@async
}

// Do stuff
```

[await]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-play-services/kotlinx.coroutines.tasks/com.google.android.gms.tasks.-task/await.html
[asTask]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-play-services/kotlinx.coroutines.tasks/kotlinx.coroutines.-deferred/as-task.html
[Maven Repository]: https://mvnrepository.com/artifact/org.jetbrains.kotlinx/kotlinx-coroutines-play-services
