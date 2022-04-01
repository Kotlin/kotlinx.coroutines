# Module kotlinx-coroutines-debug

Debugging facilities for `kotlinx.coroutines` on JVM.

### Overview

This module provides a debug JVM agent that allows to track and trace existing coroutines.
The main entry point to debug facilities is [DebugProbes] API.
Call to [DebugProbes.install] installs debug agent via ByteBuddy and starts spying on coroutines when they are created, suspended and resumed.

After that, you can use [DebugProbes.dumpCoroutines] to print all active (suspended or running) coroutines, including their state, creation and
suspension stacktraces.
Additionally, it is possible to process the list of such coroutines via [DebugProbes.dumpCoroutinesInfo] or dump isolated parts
of coroutines hierarchy referenced by a [Job] or [CoroutineScope] instances using  [DebugProbes.printJob] and [DebugProbes.printScope] respectively.

This module also provides an automatic [BlockHound](https://github.com/reactor/BlockHound) integration
that detects when a blocking operation was called in a coroutine context that prohibits it. In order to use it,
please follow the BlockHound [quick start guide](
https://github.com/reactor/BlockHound/blob/1.0.2.RELEASE/docs/quick_start.md).

### Using in your project

Add `kotlinx-coroutines-debug` to your project test dependencies:
```
dependencies {
    testImplementation 'org.jetbrains.kotlinx:kotlinx-coroutines-debug:1.4.0'
}
```

### Using in unit tests

For JUnit4 debug module provides special test rule, [CoroutinesTimeout], for installing debug probes
and to dump coroutines on timeout to simplify tests debugging.

Its usage is better demonstrated by the example (runnable code is [here](test/TestRuleExample.kt)):
 
```kotlin
class TestRuleExample {
    @get:Rule
    public val timeout = CoroutinesTimeout.seconds(1)

    private suspend fun someFunctionDeepInTheStack() {
        withContext(Dispatchers.IO) {
            delay(Long.MAX_VALUE) // Hang method
        }  
    }

    @Test
    fun hangingTest() = runBlocking {
        val job = launch {
            someFunctionDeepInTheStack()
        }
        job.join() // Join will hang
    }
}
```

After 1 second, test will fail with `TestTimeoutException` and all coroutines (`runBlocking` and `launch`) and their
stacktraces will be dumped to the console.

### Using as JVM agent

Debug module can also be used as a standalone JVM agent to enable debug probes on the application startup.
You can run your application with an additional argument: `-javaagent:kotlinx-coroutines-debug-1.6.1.jar`.
Additionally, on Linux and Mac OS X you can use `kill -5 $pid` command in order to force your application to print all alive coroutines.
When used as Java agent, `"kotlinx.coroutines.debug.enable.creation.stack.trace"` system property can be used to control 
[DebugProbes.enableCreationStackTraces] along with agent startup.

### Using in production environment

It is possible to run an application in production environments with debug probes in order to monitor its 
state and improve its observability. 
For that, it is strongly recommended to switch off [DebugProbes.enableCreationStackTraces] property to significantly 
reduce the overhead of debug probes and make it insignificant.
With creation stack-traces disabled, the typical overhead of enabled debug probes is a single-digit percentage of the total
application throughput.


### Example of usage

Capabilities of this module can be demonstrated by the following example 
(runnable code is [here](test/Example.kt)):

```kotlin
suspend fun computeValue(): String = coroutineScope {
    val one = async { computeOne() }
    val two = async { computeTwo() }
    combineResults(one, two)
}

suspend fun combineResults(one: Deferred<String>, two: Deferred<String>): String =
    one.await() + two.await()

suspend fun computeOne(): String {
    delay(5000)
    return "4"
}

suspend fun computeTwo(): String {
    delay(5000)
    return "2"
}

fun main() = runBlocking {
    DebugProbes.install()
    val deferred = async { computeValue() }
    // Delay for some time
    delay(1000)
    // Dump running coroutines
    DebugProbes.dumpCoroutines()
    println("\nDumping only deferred")
    DebugProbes.printJob(deferred)
}
```

Printed result will be:

```
Coroutines dump 2018/11/12 21:44:02

Coroutine "coroutine#2":DeferredCoroutine{Active}@289d1c02, state: SUSPENDED
	at kotlinx.coroutines.DeferredCoroutine.await$suspendImpl(Builders.common.kt:99)
	at ExampleKt.combineResults(Example.kt:11)
	at ExampleKt$computeValue$2.invokeSuspend(Example.kt:7)
	at ExampleKt$main$1$deferred$1.invokeSuspend(Example.kt:25)
	(Coroutine creation stacktrace)
	at kotlin.coroutines.intrinsics.IntrinsicsKt__IntrinsicsJvmKt.createCoroutineUnintercepted(IntrinsicsJvm.kt:116)
	at kotlinx.coroutines.intrinsics.CancellableKt.startCoroutineCancellable(Cancellable.kt:25)
	at kotlinx.coroutines.BuildersKt.async$default(Unknown Source)
	at ExampleKt$main$1.invokeSuspend(Example.kt:25)
	at kotlin.coroutines.jvm.internal.BaseContinuationImpl.resumeWith(ContinuationImpl.kt:32)
	at kotlinx.coroutines.DispatchedTask.run(Dispatched.kt:233)
	at kotlinx.coroutines.BuildersKt.runBlocking$default(Unknown Source)
	at ExampleKt.main(Example.kt:23)
	at ExampleKt.main(Example.kt)

... More coroutines here ...

Dumping only deferred
"coroutine#2":DeferredCoroutine{Active}, continuation is SUSPENDED at line kotlinx.coroutines.DeferredCoroutine.await$suspendImpl(Builders.common.kt:99)
    "coroutine#3":DeferredCoroutine{Active}, continuation is SUSPENDED at line ExampleKt.computeOne(Example.kt:14)
    "coroutine#4":DeferredCoroutine{Active}, continuation is SUSPENDED at line ExampleKt.computeTwo(Example.kt:19)
```

### Status of the API

API is experimental, and it is not guaranteed it won't be changed (while it is marked as `@ExperimentalCoroutinesApi`).
Like the rest of experimental API, `DebugProbes` is carefully designed, tested and ready to use in both test and production 
environments. It is marked as experimental to leave us the room to enrich the output data in a potentially backwards incompatible manner
to further improve diagnostics and debugging experience.

The output format of [DebugProbes] can be changed in the future and it is not recommended to rely on the string representation
of the dump programmatically.

### Debug agent and Android

Android runtime does not support Instrument API necessary for `kotlinx-coroutines-debug` to function, triggering `java.lang.NoClassDefFoundError: Failed resolution of: Ljava/lang/management/ManagementFactory;`,
and it is not possible to use coroutine debugger along with Android emulator.

<!---
Make an exception googlable
java.lang.NoClassDefFoundError: Failed resolution of: Ljava/lang/management/ManagementFactory;
        at kotlinx.coroutines.repackaged.net.bytebuddy.agent.ByteBuddyAgent$ProcessProvider$ForCurrentVm$ForLegacyVm.resolve(ByteBuddyAgent.java:1055)
        at kotlinx.coroutines.repackaged.net.bytebuddy.agent.ByteBuddyAgent$ProcessProvider$ForCurrentVm.resolve(ByteBuddyAgent.java:1038)
        at kotlinx.coroutines.repackaged.net.bytebuddy.agent.ByteBuddyAgent.install(ByteBuddyAgent.java:374)
        at kotlinx.coroutines.repackaged.net.bytebuddy.agent.ByteBuddyAgent.install(ByteBuddyAgent.java:342)
        at kotlinx.coroutines.repackaged.net.bytebuddy.agent.ByteBuddyAgent.install(ByteBuddyAgent.java:328)
        at kotlinx.coroutines.debug.internal.DebugProbesImpl.install(DebugProbesImpl.kt:39)
        at kotlinx.coroutines.debug.DebugProbes.install(DebugProbes.kt:49)
-->

#### Build failures due to duplicate resource files

Building an Android project that depends on `kotlinx-coroutines-debug` (usually introduced by being a transitive
dependency of `kotlinx-coroutines-test`) may fail with `DuplicateRelativeFileException` for `META-INF/AL2.0`,
`META-INF/LGPL2.1`, or `win32-x86/attach_hotspot_windows.dll` when trying to merge the Android resource.

The problem is that Android merges the resources of all its dependencies into a single directory and complains about
conflicts, but:
* `kotlinx-coroutines-debug` transitively depends on JNA and JNA-platform, both of which include license files in their
  META-INF directories. Trying to merge these files leads to conflicts, which means that any Android project that
  depends on JNA and JNA-platform will experience build failures.
* Additionally, `kotlinx-coroutines-debug` embeds `byte-buddy-agent` and `byte-buddy`, along with their resource files.
  Then, if the project separately depends on `byte-buddy`, merging the resources of `kotlinx-coroutines-debug` with ones
  from `byte-buddy` and `byte-buddy-agent` will lead to conflicts as the resource files are duplicated.

One possible workaround for these issues is to add the following to the `android` block in your gradle file for the
application subproject:
```groovy
     packagingOptions {
         // for JNA and JNA-platform
         exclude "META-INF/AL2.0"
         exclude "META-INF/LGPL2.1"
         // for byte-buddy
         exclude "META-INF/licenses/ASM"
         pickFirst "win32-x86-64/attach_hotspot_windows.dll"
         pickFirst "win32-x86/attach_hotspot_windows.dll"
     }
```
This will cause the resource merge algorithm to exclude the problematic license files altogether and only leave a single
copy of the files needed for `byte-buddy-agent` to work.

Alternatively, avoid depending on `kotlinx-coroutines-debug`. In particular, if the only reason why this library a
dependency of your project is that `kotlinx-coroutines-test` in turn depends on it, you may change your dependency on
`kotlinx.coroutines.test` to exclude `kotlinx-coroutines-debug`. For example, you could replace
```kotlin
androidTestImplementation("org.jetbrains.kotlinx:kotlinx-coroutines-test:$coroutines_version")
```
with
```groovy
androidTestImplementation("org.jetbrains.kotlinx:kotlinx-coroutines-test:$coroutines_version") {
    exclude group: "org.jetbrains.kotlinx", module: "kotlinx-coroutines-debug"
}
```
<!---
Snippets of stacktraces for googling:

org.gradle.api.tasks.TaskExecutionException: Execution failed for task ':app:mergeDebugAndroidTestJavaResource'.
        ...
Caused by: org.gradle.workers.intelrnal.DefaultWorkerExecutor$WorkExecutionException: A failure occurred while executing com.android.build.gradle.internal.tasks.Workers$ActionFacade
        ...
Caused by: com.android.builder.merge.DuplicateRelativeFileException: More than one file was found with OS independent path 'META-INF/AL2.0'.
        at com.android.builder.merge.StreamMergeAlgorithms.lambda$acceptOnlyOne$2(StreamMergeAlgorithms.java:85)
        at com.android.builder.merge.StreamMergeAlgorithms.lambda$select$3(StreamMergeAlgorithms.java:106)
        at com.android.builder.merge.IncrementalFileMergerOutputs$1.create(IncrementalFileMergerOutputs.java:88)
        at com.android.builder.merge.DelegateIncrementalFileMergerOutput.create(DelegateIncrementalFileMergerOutput.java:64)
        at com.android.build.gradle.internal.tasks.MergeJavaResourcesDelegate$run$output$1.create(MergeJavaResourcesDelegate.kt:230)
        at com.android.builder.merge.IncrementalFileMerger.updateChangedFile(IncrementalFileMerger.java:242)
        at com.android.builder.merge.IncrementalFileMerger.mergeChangedInputs(IncrementalFileMerger.java:203)
        at com.android.builder.merge.IncrementalFileMerger.merge(IncrementalFileMerger.java:80)
        at com.android.build.gradle.internal.tasks.MergeJavaResourcesDelegate.run(MergeJavaResourcesDelegate.kt:276)
        at com.android.build.gradle.internal.tasks.MergeJavaResRunnable.run(MergeJavaResRunnable.kt:81)
        at com.android.build.gradle.internal.tasks.Workers$ActionFacade.run(Workers.kt:242)
        at org.gradle.workers.internal.AdapterWorkAction.execute(AdapterWorkAction.java:50)
        at org.gradle.workers.internal.DefaultWorkerServer.execute(DefaultWorkerServer.java:50)
        at org.gradle.workers.internal.NoIsolationWorkerFactory$1$1.create(NoIsolationWorkerFactory.java:63)
        at org.gradle.workers.internal.NoIsolationWorkerFactory$1$1.create(NoIsolationWorkerFactory.java:59)
        at org.gradle.internal.classloader.ClassLoaderUtils.executeInClassloader(ClassLoaderUtils.java:98)
        at org.gradle.workers.internal.NoIsolationWorkerFactory$1.lambda$execute$0(NoIsolationWorkerFactory.java:59)
        at org.gradle.workers.internal.AbstractWorker$1.call(AbstractWorker.java:44)
        at org.gradle.workers.internal.AbstractWorker$1.call(AbstractWorker.java:41)
        at org.gradle.internal.operations.DefaultBuildOperationExecutor$CallableBuildOperationWorker.execute(DefaultBuildOperationExecutor.java:416)
        at org.gradle.internal.operations.DefaultBuildOperationExecutor$CallableBuildOperationWorker.execute(DefaultBuildOperationExecutor.java:406)
        at org.gradle.internal.operations.DefaultBuildOperationExecutor$1.execute(DefaultBuildOperationExecutor.java:165)
        at org.gradle.internal.operations.DefaultBuildOperationExecutor.execute(DefaultBuildOperationExecutor.java:250)
        at org.gradle.internal.operations.DefaultBuildOperationExecutor.execute(DefaultBuildOperationExecutor.java:158)
        at org.gradle.internal.operations.DefaultBuildOperationExecutor.call(DefaultBuildOperationExecutor.java:102)
        at org.gradle.internal.operations.DelegatingBuildOperationExecutor.call(DelegatingBuildOperationExecutor.java:36)
        at org.gradle.workers.internal.AbstractWorker.executeWrappedInBuildOperation(AbstractWorker.java:41)
        at org.gradle.workers.internal.NoIsolationWorkerFactory$1.execute(NoIsolationWorkerFactory.java:53)
        at org.gradle.workers.internal.DefaultWorkerExecutor.lambda$submitWork$2(DefaultWorkerExecutor.java:200)
        at org.gradle.internal.work.DefaultConditionalExecutionQueue$ExecutionRunner.runExecution(DefaultConditionalExecutionQueue.java:215)
        at org.gradle.internal.work.DefaultConditionalExecutionQueue$ExecutionRunner.runBatch(DefaultConditionalExecutionQueue.java:164)
        at org.gradle.internal.work.DefaultConditionalExecutionQueue$ExecutionRunner.run(DefaultConditionalExecutionQueue.java:131)

Execution failed for task ':app:mergeStagingDebugAndroidTestJavaResource'.
Execution failed for task ':app:mergeDebugAndroidTestJavaResource'.
Execution failed for task ':app:mergeDebugTestJavaResource'

More than one file was found with OS independent path 'META-INF/LGPL2.1'
More than one file was found with OS independent path 'win32-x86/attach_hotspot_windows.dll'
More than one file was found with OS independent path 'win32-x86-64/attach_hotspot_windows.dll'
-->
<!--- MODULE kotlinx-coroutines-core -->
<!--- INDEX kotlinx.coroutines -->

[Job]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-job/index.html
[CoroutineScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-coroutine-scope/index.html

<!--- MODULE kotlinx-coroutines-debug -->
<!--- INDEX kotlinx.coroutines.debug -->

[DebugProbes]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-debug/kotlinx.coroutines.debug/-debug-probes/index.html
[DebugProbes.install]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-debug/kotlinx.coroutines.debug/-debug-probes/install.html
[DebugProbes.dumpCoroutines]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-debug/kotlinx.coroutines.debug/-debug-probes/dump-coroutines.html
[DebugProbes.dumpCoroutinesInfo]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-debug/kotlinx.coroutines.debug/-debug-probes/dump-coroutines-info.html
[DebugProbes.printJob]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-debug/kotlinx.coroutines.debug/-debug-probes/print-job.html
[DebugProbes.printScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-debug/kotlinx.coroutines.debug/-debug-probes/print-scope.html
[DebugProbes.enableCreationStackTraces]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-debug/kotlinx.coroutines.debug/-debug-probes/enable-creation-stack-traces.html

<!--- INDEX kotlinx.coroutines.debug.junit4 -->

[CoroutinesTimeout]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-debug/kotlinx.coroutines.debug.junit4/-coroutines-timeout/index.html

<!--- END -->
