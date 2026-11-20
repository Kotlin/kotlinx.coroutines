<contribute-url>https://github.com/Kotlin/kotlinx.coroutines/edit/master/docs/topics/</contribute-url>

[//]: # (title: Coroutines guide)

Kotlin provides only minimal low-level APIs in its standard library to enable other 
libraries to utilize coroutines. Unlike many other languages with similar capabilities, `async` and `await`
are not keywords in Kotlin and are not even part of its standard library. Moreover, Kotlin's concept
of _suspending function_ provides a safer and less error-prone abstraction for asynchronous 
operations than futures and promises.  

`kotlinx.coroutines` is a rich library for coroutines developed by JetBrains. It contains a number of high-level 
coroutine-enabled primitives that this guide covers, including `.launch()`, `.async()`, and others. 

This is a guide about the core features of `kotlinx.coroutines` with a series of examples, divided up into different topics.
If you prefer learning through videos, watch the [Kotlin Coroutines: Full 4-Hour Course from Sebastian Aigner](https://www.youtube.com/watch?v=2kkvXR-J45E).
It covers coroutine fundamentals with practical examples and exercises on structured concurrency, cancellation, exception handling, and flows.

To use coroutines, [add a dependency](coroutines-basics.md#add-the-kotlinx-coroutines-library-to-your-project) on the `kotlinx-coroutines-core` module.

## Table of contents

* [Coroutines basics](coroutines-basics.md)
* [Tutorial: Introduction to coroutines and flows](coroutines-and-flows-tutorial.md)
* [Cancellation and timeouts](coroutines-cancellation.md)
* [Flows](coroutines-flow.md)
* [Composing suspending functions](composing-suspending-functions.md)
* [Coroutine context and dispatchers](coroutine-context-and-dispatchers.md)
* [Debug coroutines](coroutines-debugging.md)
* [Channels](channels.md)
* [Coroutine exceptions handling](exception-handling.md)
* [Shared mutable state and concurrency](shared-mutable-state-and-concurrency.md)
* [Select expression (experimental)](select-expression.md)
* [Tutorial: Debug coroutines using IntelliJ IDEA](debug-coroutines-with-idea.md)
* [Tutorial: Debug Kotlin Flow using IntelliJ IDEA](debug-flow-with-idea.md)

## Additional references

* [Guide to UI programming with coroutines](https://github.com/Kotlin/kotlinx.coroutines/blob/master/ui/coroutines-guide-ui.md)
* [Coroutines design document (KEEP)](https://github.com/Kotlin/KEEP/blob/master/proposals/coroutines.md)
* [Full kotlinx.coroutines API reference](https://kotlinlang.org/api/kotlinx.coroutines/)
* [Best practices for coroutines in Android](https://developer.android.com/kotlin/coroutines/coroutines-best-practices)
* [Additional Android resources for Kotlin coroutines and flow](https://developer.android.com/kotlin/coroutines/additional-resources)
