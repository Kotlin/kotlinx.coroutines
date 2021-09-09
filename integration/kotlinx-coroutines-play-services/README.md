# Module kotlinx-coroutines-play-services

Integration with Google Play Services [Tasks API](https://developers.google.com/android/guides/tasks).

Extension functions:

| **Name** | **Description**
| -------- | ---------------
| [Task.asDeferred][asDeferred] | Converts a Task into a Deferred
| [Task.await][await] | Awaits for completion of the Task (cancellable)
| [Deferred.asTask][asTask] | Converts a deferred value to a Task

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

If the `Task` supports cancellation via passing a `CancellationToken`, pass the corresponding `CancellationTokenSource` to `asDeferred` or `await` to support bi-directional cancellation:

```kotlin
val cancellationTokenSource = CancellationTokenSource()
val currentLocationTask = fusedLocationProviderClient.getCurrentLocation(PRIORITY_HIGH_ACCURACY, cancellationTokenSource.token)
val currentLocation = currentLocationTask.await(cancellationTokenSource) // cancelling `await` also cancels `currentLocationTask`, and vice versa
```


<!--- MODULE kotlinx-coroutines-play-services -->
<!--- INDEX kotlinx.coroutines.tasks -->

[asDeferred]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-play-services/kotlinx.coroutines.tasks/as-deferred.html
[await]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-play-services/kotlinx.coroutines.tasks/await.html
[asTask]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-play-services/kotlinx.coroutines.tasks/as-task.html

<!--- END -->
