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

### Using in your project

Add `kotlinx-coroutines-debug` to your project test dependencies:
```
dependencies {
    testImplementation 'org.jetbrains.kotlinx:kotlinx-coroutines-debug:1.3.4'
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
You can run your application with an additional argument: `-javaagent:kotlinx-coroutines-debug-1.3.4.jar`.
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

Unfortunately, Android runtime does not support Instrument API necessary for `kotlinx-coroutines-debug` to function, triggering `java.lang.NoClassDefFoundError: Failed resolution of: Ljava/lang/management/ManagementFactory;`.

Nevertheless, it will be possible to support debug agent on Android as soon as [GradleAspectJ-Android](https://github.com/Archinamon/android-gradle-aspectj)  will support android-gradle 3.3 

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
