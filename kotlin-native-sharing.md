# Sharing and background threads on Kotlin/Native

## Preview disclaimer

This is a preview release of sharing and backgrounds threads for coroutines on Kotlin/Native. 
Details of this implementation will change in the future. See also [Known Problems](#known-problems)
at the end of this document.

## Introduction

Kotlin/Native provides an automated memory management that works with mutable data objects separately 
and independently in each thread that uses Kotlin/Native runtime. Sharing data between threads is limited:

* Objects to be shared between threads can be [frozen](https://kotlinlang.org/api/latest/jvm/stdlib/kotlin.native.concurrent/freeze.html).
  This makes the whole object graph deeply immutable and allows to share it between threads.
* Mutable objects can be wrapped into [DetachedObjectGraph](https://kotlinlang.org/api/latest/jvm/stdlib/kotlin.native.concurrent/-detached-object-graph/index.html)
  on one thread and later reattached onto the different thread.

This introduces several differences between Kotlin/JVM and Kotlin/Native in terms of coroutines that must
be accounted for when writing cross-platform applications. 
  
## Threads and dispatchers

An active coroutine has a mutable state. It cannot migrate from thread to thread. A coroutine in Kotlin/Native
is always bound to a specific thread. Coroutines that are detached from a thread are currently not supported.

`kotlinx.coroutines` provides ability to create single-threaded dispatchers for background work
via [newSingleThreadContext] function that is available for both Kotlin/JVM and Kotlin/Native. It is not
recommended shutting down such a dispatcher on Kotlin/Native via [SingleThreadDispatcher.close] function
while the application still working unless you are absolutely sure all coroutines running in this
dispatcher have completed. Unlike Kotlin/JVM, there is no backup default thread that might
execute cleanup code for coroutines that might have been still working in this dispatcher.

For interoperability with code that is using Kotlin/Native 
[Worker](https://kotlinlang.org/api/latest/jvm/stdlib/kotlin.native.concurrent/-worker/index.html)
API you can get a reference to single-threaded dispacher's worker using its [SingleThreadDispatcher.worker] property.

A [Default][Dispatchers.Default] dispatcher on Kotlin/Native contains a single background thread.
This is the dispatcher that is used by default in [GlobalScope]. 

> This limitation may be lifted in the future with the default dispatcher becoming multi-threaded and/or
> its coroutines becoming isolated from each other, so please do not assume that different coroutines running 
> in the default dispatcher can share mutable data between themselves. 

A [Main][Dispatchers.Main] dispatcher is
properly defined for all Darwin (Apple) targets, refers to the main thread, and integrates
with Core Foundation main event loop. 
On Linux and Windows there is no platform-defined main thread, so [Main][Dispatchers.Main] simply refers
to the current thread that must have been either created with `newSingleThreadContext` or be running
inside [runBlocking] function.

The main thread of application has two options on using coroutines.
A backend application's main thread shall use [runBlocking].
A UI application running on one Apple's Darwin OSes shall run
its main queue event loop using `NSRunLoopRun`, `UIApplicationMain`, or ` NSApplicationMain`.
For example, that is how you can have main dispatcher in your own `main` function: 

```kotlin
fun main() {
    val mainScope = MainScope()
    mainScope.launch { /* coroutine in the main thread */ } 
    CFRunLoopRun() // run event loop    
}
```
 
## Switching threads

You switch from one dispatcher to another using a regular [withContext] function. For example, a code running 
on the main thread might do:

```kotlin                
// in the main thead
val result = withContext(Dispatcher.Default) {
    // now executing in background thread 
}                                        
// now back to the main thread
result // use result here
```
   
If you capture a reference to any object that is defined in the main thread outside of `withContext` into the
block inside `withContext` then it gets automatically frozen for transfer from the main thread to the
background thread. Freezing is recursive, so you might accidentally freeze unrelated objects that are part of
main thread's mutable state and get 
[InvalidMutabilityException](https://kotlinlang.org/api/latest/jvm/stdlib/kotlin.native.concurrent/-invalid-mutability-exception/index.html)
later in unrelated parts of your code.
The easiest way to trouble-shoot it is to mark the objects that should not have been frozen using 
[ensureNeverFrozen](https://kotlinlang.org/api/latest/jvm/stdlib/kotlin.native.concurrent/ensure-never-frozen.html)
function so that you get exception in the very place they were frozen that would pinpoint the corresponding
`withContext` call in your code.

The `result` of `withContext` call can be used after `withContext` call. It gets automatically frozen
for transfer from background to the main thread, too. 

A disciplined use of threads in Kotlin/Native is to transfer only immutable data between the threads. 
Such code works equally well both on Kotlin/JVM and Kotlin/Native.      
  
> Note: freezing only happens when `withContext` changes from one thread to another. If you call 
> `withContext` and execution stays in the same thread, then there is not freezing and mutable data
> can be captured and operated on as usual.

The same rule on freezing applies to coroutines launched with any builder like [launch], [async], [produce], etc.     
  
## Communication objects  
  
All core communication and synchronization objects in `kotlin.coroutines` such as 
[Job], [Deferred], [Channel], [BroadcastChannel], [Mutex], and [Semaphore] are _shareable_.
It means that they can be frozen for sharing with another thread and still continue to operate normally.
Any object that is transferred via a frozen (shared) [Deferred] or any [Channel] is also automatically frozen.

Similar rules apply to [Flow]. When an instance of a [Flow] itself is shared (frozen), then all the references that
are captured in to the lambdas in this flow operators are frozen. Regardless of whether the flow instance itself
was frozen, by default, the whole flow operates in a single thread, so mutable data can freely travel down the 
flow from emitter to collector. However, when [flowOn] operator is used to change the thread, then 
objects crossing the thread boundary get frozen.  

Note, that if you protect any piece of mutable data with a [Mutex] or a [Semaphore] then it does not
automatically become shareable. In order to share mutable data you have to either 
wrap it into [DetachedObjectGraph](https://kotlinlang.org/api/latest/jvm/stdlib/kotlin.native.concurrent/-detached-object-graph/index.html)  
or use atomic classes ([AtomicInt](https://kotlinlang.org/api/latest/jvm/stdlib/kotlin.native.concurrent/-atomic-int/index.html), etc).

## Cyclic garbage

Code working in a single thread on Kotlin/Native enjoys fully automatic memory management. Any object graph that
is not referenced anymore is automatically reclaimed even if it contains cyclic chains of references. This does
not extend to shared objects, though. Frozen immutable objects can be freely shared, even if then can contain
reference cycles, but shareable [communication objects](#communication-objects) leak if a reference cycle
to them appears. The easiest way to demonstrate it is to return a reference to a [async] coroutine as its result, 
so that the resulting [Deferred] contains a reference to itself:

```kotlin       
// from the main thread call coroutine in a background thread or otherwise share it
val result = GlobalScope.async {
    coroutineContext // return its coroutine context that contains a self-reference
}
// now result will not be reclaimed -- memory leak
```    

A disciplined use of communication objects to transfer immutable data between coroutines does not 
result in any memory reclamation problems. 

## Shared channels are resources

All kinds of [Channel] and [BroadcastChannel] implementations become _resources_ on Kotlin/Native when shared. 
They must be closed and fully consumed in order for their memory to be reclaimed. When they are not shared, they 
can be dropped in any state and will be reclaimed by memory manager, but a shared channel generally will not be reclaimed
unless closed and consumed.

This does not affect [Flow], because it is a cold abstraction. Even though [Flow] internally uses channels to transfer
data between threads, it always properly closes these channels when completing collection of data.

## Known problems

The current implementation is tested and works for all kinds of single-threaded cases and simple scenarios that
transfer data between two thread like shown in [Switching Threads](#switching-threads) section. However, it is known
to leak memory in scenarios involving concurrency under load, for example when multiple children coroutines running 
in different threads are simultaneously cancelled. 
                                                           
<!--- MODULE kotlinx-coroutines-core -->
<!--- INDEX kotlinx.coroutines -->
[newSingleThreadContext]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/new-single-thread-context.html
[SingleThreadDispatcher.close]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-single-thread-dispatcher/-single-thread-dispatcher/close.html
[SingleThreadDispatcher.worker]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-single-thread-dispatcher/-single-thread-dispatcher/worker.html
[Dispatchers.Default]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-dispatchers/-default.html
[GlobalScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-global-scope/index.html
[Dispatchers.Main]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-dispatchers/-main.html
[runBlocking]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/run-blocking.html
[withContext]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/with-context.html
[launch]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/launch.html
[async]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/async.html
[Job]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-job/index.html
[Deferred]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-deferred/index.html
<!--- INDEX kotlinx.coroutines.flow -->
[Flow]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/-flow/index.html
[flowOn]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/flow-on.html
<!--- INDEX kotlinx.coroutines.channels -->
[produce]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/produce.html
[Channel]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-channel/index.html
[BroadcastChannel]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-broadcast-channel/index.html
<!--- INDEX kotlinx.coroutines.selects -->
<!--- INDEX kotlinx.coroutines.sync -->
[Mutex]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.sync/-mutex/index.html
[Semaphore]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.sync/-semaphore/index.html
<!--- END -->
 
