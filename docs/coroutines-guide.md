
Kotlin, as a language, provides only minimal low-level APIs in its standard library to enable various other 
libraries to utilize coroutines. Unlike many other languages with similar capabilities, `async` and `await`
are not keywords in Kotlin and are not even part of its standard library. Moreover, Kotlin's concept
of _suspending function_ provides a safer and less error-prone abstraction for for asynchronous 
operations than futures and promises.  

`kotlinx.coroutines` is a rich library for coroutines developed by JetBrains. It contains a number of high-level 
coroutine-enabled primitives that this guide covers, including `launch`, `async` and others. 

This is a guide on core features of `kotlinx.coroutines` with a series of examples, divided up into different topics.

In order to use coroutines as well as follow the examples in this guide, you need to add a dependency on `kotlinx-coroutines-core` module as explained 
[in the project README ](../README.md#using-in-your-projects).

## Table of contents

* [Coroutine basics](basics.md)
* [Cancellation and timeouts](cancellation-and-timeouts.md)
* [Composing suspending functions](composing-suspending-functions.md)
* [Coroutine context and dispatchers](coroutine-context-and-dispatchers.md)
* [Exception handling and supervision](exception-handling.md)
* [Channels (experimental)](channels.md)
* [Shared mutable state and concurrency](shared-mutable-state-and-concurrency.md)
* [Select expression (experimental)](select-expression.md)

## Additional references

* [Guide to UI programming with coroutines](../ui/coroutines-guide-ui.md)
* [Guide to reactive streams with coroutines](../reactive/coroutines-guide-reactive.md)
* [Coroutines design document (KEEP)](https://github.com/Kotlin/kotlin-coroutines/blob/master/kotlin-coroutines-informal.md)
* [Full kotlinx.coroutines API reference](http://kotlin.github.io/kotlinx.coroutines)