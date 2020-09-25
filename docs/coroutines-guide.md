
Kotlin, as a language, provides only minimal low-level APIs in its standard library to enable various other 
libraries to utilize coroutines. Unlike many other languages with similar capabilities, `async` and `await`
are not keywords in Kotlin and are not even part of its standard library. Moreover, Kotlin's concept
of _suspending function_ provides a safer and less error-prone abstraction for asynchronous 
operations than futures and promises.  

`kotlinx.coroutines` is a rich library for coroutines developed by JetBrains. It contains a number of high-level 
coroutine-enabled primitives that this guide covers, including `launch`, `async` and others. 

This is a guide on core features of `kotlinx.coroutines` with a series of examples, divided up into different topics.

In order to use coroutines as well as follow the examples in this guide, you need to add a dependency on the `kotlinx-coroutines-core` module as explained 
[in the project README](../README.md#using-in-your-projects).

## Table of contents

* [Basics](basics.md)
* [Cancellation and Timeouts](cancellation-and-timeouts.md)
* [Composing Suspending Functions](composing-suspending-functions.md)
* [Coroutine Context and Dispatchers](coroutine-context-and-dispatchers.md)
* [Asynchronous Flow](flow.md)
* [Channels](channels.md)
* [Exception Handling and Supervision](exception-handling.md)
* [Shared Mutable State and Concurrency](shared-mutable-state-and-concurrency.md)
* [Select Expression (experimental)](select-expression.md)

## Additional references

* [Guide to UI programming with coroutines](../ui/coroutines-guide-ui.md)
* [Coroutines design document (KEEP)](https://github.com/Kotlin/kotlin-coroutines/blob/master/kotlin-coroutines-informal.md)
* [Full kotlinx.coroutines API reference](https://kotlin.github.io/kotlinx.coroutines)
