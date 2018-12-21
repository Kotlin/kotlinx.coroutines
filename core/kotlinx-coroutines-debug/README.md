# Module kotlinx-coroutines-debug

Debugging facilities for `kotlinx.coroutines` on JVM.

### Overview

This module provides a debug JVM agent that allows to track and trace existing coroutines.
The main entry point to debug facilities is [DebugProbes] API.
Call to [DebugProbes.install] installs debug agent via ByteBuddy and starts spying on coroutines when they are created, suspended and resumed.

After that, you can use [DebugProbes.dumpCoroutines] to print all active (suspended or running) coroutines, including their state, creation and
suspension stacktraces.
Additionally, it is possible to process the list of such coroutines via [DebugProbes.dumpCoroutinesState] or dump isolated parts
of coroutines hierarchy referenced by a [Job] or [CoroutineScope] instances using  [DebugProbes.printJob] and [DebugProbes.printScope] respectively.

### Using in your project

Add `kotlinx-coroutines-debug` to your project test dependencies:
```
dependencies {
    testImplementation 'org.jetbrains.kotlinx:kotlinx-coroutines-debug:1.1.0'
}
```

### Using as JVM agent

It is possible to use this module as a standalone JVM agent to enable debug probes on the application startup.
You can run your application with an additional argument: `-javaagent:kotlinx-coroutines-debug-1.1.0.jar`.
Additionally, on Linux and Mac OS X you can use `kill -5 $pid` command in order to force your application to print all alive coroutines.


### Example of usage

Capabilities of this module can be demonstrated by the following example:
```kotlin
class Computation {
    public fun computeValue(): Deferred<String> = GlobalScope.async {
        val firstPart = computeFirstPart()
        val secondPart = computeSecondPart()

        combineResults(firstPart, secondPart)
    }

    private suspend fun combineResults(firstPart: Deferred<String>, secondPart: Deferred<String>): String {
        return firstPart.await() + secondPart.await()
    }


    private suspend fun CoroutineScope.computeFirstPart() = async {
        delay(5000)
        "4"
    }

    private suspend fun CoroutineScope.computeSecondPart() = async {
        delay(5000)
        "2"
    }
}

fun main(args: Array<String>) = runBlocking {
    DebugProbes.install()
    val computation = Computation()
    val deferred = computation.computeValue()

    // Delay for some time
    delay(1000)

    DebugProbes.dumpCoroutines()

    println("\nDumping only deferred")
    DebugProbes.printJob(deferred)
}
```

Printed result will be:
```
Coroutines dump 2018/11/12 21:44:02

Coroutine "coroutine#2":DeferredCoroutine{Active}@1b26f7b2, state: SUSPENDED
	at kotlinx.coroutines.DeferredCoroutine.await$suspendImpl(Builders.common.kt:99)
	at Computation.combineResults(Example.kt:18)
	at Computation$computeValue$1.invokeSuspend(Example.kt:14)
	(Coroutine creation stacktrace)
	at kotlin.coroutines.intrinsics.IntrinsicsKt__IntrinsicsJvmKt.createCoroutineUnintercepted(IntrinsicsJvm.kt:116)
	at kotlinx.coroutines.intrinsics.CancellableKt.startCoroutineCancellable(Cancellable.kt:23)
	at kotlinx.coroutines.CoroutineStart.invoke(CoroutineStart.kt:109)
	at kotlinx.coroutines.AbstractCoroutine.start(AbstractCoroutine.kt:160)
	at kotlinx.coroutines.BuildersKt__Builders_commonKt.async(Builders.common.kt:88)
	at kotlinx.coroutines.BuildersKt.async(Unknown Source)
	at kotlinx.coroutines.BuildersKt__Builders_commonKt.async$default(Builders.common.kt:81)
	at kotlinx.coroutines.BuildersKt.async$default(Unknown Source)
	at Computation.computeValue(Example.kt:10)
	at ExampleKt$main$1.invokeSuspend(Example.kt:36)
	at kotlin.coroutines.jvm.internal.BaseContinuationImpl.resumeWith(ContinuationImpl.kt:32)
	at kotlinx.coroutines.DispatchedTask$DefaultImpls.run(Dispatched.kt:237)
	at kotlinx.coroutines.DispatchedContinuation.run(Dispatched.kt:81)
	at kotlinx.coroutines.EventLoopBase.processNextEvent(EventLoop.kt:123)
	at kotlinx.coroutines.BlockingCoroutine.joinBlocking(Builders.kt:69)
	at kotlinx.coroutines.BuildersKt__BuildersKt.runBlocking(Builders.kt:45)
	at kotlinx.coroutines.BuildersKt.runBlocking(Unknown Source)
	at kotlinx.coroutines.BuildersKt__BuildersKt.runBlocking$default(Builders.kt:35)
	at kotlinx.coroutines.BuildersKt.runBlocking$default(Unknown Source)
	at ExampleKt.main(Example.kt:33)

... More coroutines here ...

Dumping only deferred
"coroutine#2":DeferredCoroutine{Active}, continuation is SUSPENDED at line kotlinx.coroutines.DeferredCoroutine.await$suspendImpl(Builders.common.kt:99)
	"coroutine#3":DeferredCoroutine{Active}, continuation is SUSPENDED at line Computation$computeFirstPart$2.invokeSuspend(Example.kt:23)
	"coroutine#4":DeferredCoroutine{Active}, continuation is SUSPENDED at line Computation$computeSecondPart$2.invokeSuspend(Example.kt:28)
```


### Status of the API

API is purely experimental and it is not guaranteed that it won't be changed (while it is marked as `@ExperimentalCoroutinesApi`).
Do not use this module in production environment and do not rely on the format of the data produced by [DebugProbes]. 

<!--- MODULE kotlinx-coroutines-core -->
<!--- INDEX kotlinx.coroutines -->
[Job]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-job/index.html
[CoroutineScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-coroutine-scope/index.html
<!--- MODULE kotlinx-coroutines-debug -->
<!--- INDEX kotlinx.coroutines.debug -->
[DebugProbes]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-debug/kotlinx.coroutines.debug/-debug-probes/index.html
[DebugProbes.install]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-debug/kotlinx.coroutines.debug/-debug-probes/install.html
[DebugProbes.dumpCoroutines]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-debug/kotlinx.coroutines.debug/-debug-probes/dump-coroutines.html
[DebugProbes.dumpCoroutinesState]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-debug/kotlinx.coroutines.debug/-debug-probes/dump-coroutines-state.html
[DebugProbes.printScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-debug/kotlinx.coroutines.debug/-debug-probes/print-scope.html
[DebugProbes.printJob]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-debug/kotlinx.coroutines.debug/-debug-probes/print-job.html
<!--- END -->
