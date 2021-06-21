# Module kotlinx-coroutines-huawei-services

Integration with Huawei Mobile Services [Tasks API](https://developer.huawei.com/consumer/en/doc/HMSCore-References-V5/tasks-overview-0000001050202661-V5).

Extension functions:

| **Name** | **Description**
| -------- | ---------------
| [Task.await][await] | Awaits for completion of the Task
| [Task.asDeferred][asDeferred] | Awaits for a result of the Task
| [Deferred.asTask][asTask] | Converts a deferred value to a Task

## Example
```kotlin
val locationProviderClient = LocationServices.getFusedLocationProviderClient(context)

scope.launch {
    val location: Location = locationProviderClient.getLastLocation().await()
}

val deferredLocation = locationProviderClient.getLastLocation().asDeferred()
```

[await]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-huawei-services/kotlinx.coroutines.tasks/com.huawei.hmf.tasks.-task/await.html
[asDeferred]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-huawei-services/kotlinx.coroutines.tasks/com.huawei.hmf.tasks.-task/as-deferred.html
[asTask]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-huawei-services/kotlinx.coroutines.tasks/kotlinx.coroutines.-deferred/as-task.html
