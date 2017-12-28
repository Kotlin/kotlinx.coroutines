---
title: kotlinx-coroutines
layout: api
---

# kotlinx.coroutines reference documentation

Library support for Kotlin coroutines. This reference is a companion to 
[Guide to kotlinx.coroutines by example](https://github.com/Kotlin/kotlinx.coroutines/blob/master/coroutines-guide.md).

## Modules

| Name                                                       | Description                                      |
| ---------------------------------------------------------- | ------------------------------------------------ |
| [kotlinx-coroutines-core](kotlinx-coroutines-core)         | Core primitives to work with coroutines          |
| [kotlinx-coroutines-io](kotlinx-coroutines-io)             | Byte I/O channels (_unstable_, work in progress) |
| [kotlinx-coroutines-reactive](kotlinx-coroutines-reactive) | Utilities for [Reactive Streams](http://www.reactive-streams.org) |
| [kotlinx-coroutines-reactor](kotlinx-coroutines-reactor)   | Utilities for [Reactor](https://projectreactor.io) |
| [kotlinx-coroutines-rx1](kotlinx-coroutines-rx1)           | Utilities for [RxJava 1.x](https://github.com/ReactiveX/RxJava/tree/1.x) |
| [kotlinx-coroutines-rx2](kotlinx-coroutines-rx2)           | Utilities for [RxJava 2.x](https://github.com/ReactiveX/RxJava) |
| [kotlinx-coroutines-android](kotlinx-coroutines-android)   | `UI` context for Android applications |
| [kotlinx-coroutines-javafx](kotlinx-coroutines-javafx)     | `JavaFx` context for JavaFX UI applications |
| [kotlinx-coroutines-swing](kotlinx-coroutines-swing)       | `Swing` context for Swing UI applications |
| [kotlinx-coroutines-jdk8](kotlinx-coroutines-jdk8)         | Integration with JDK8 `CompletableFuture` (Android API level 24) |
| [kotlinx-coroutines-nio](kotlinx-coroutines-nio)           | Integration with asynchronous IO on JDK7+ (Android O Preview) |
| [kotlinx-coroutines-guava](kotlinx-coroutines-guava)       | Integration with Guava [ListenableFuture](https://github.com/google/guava/wiki/ListenableFutureExplained) |
| [kotlinx-coroutines-quasar](kotlinx-coroutines-quasar)     | Integration with [Quasar](http://docs.paralleluniverse.co/quasar/) |

## Examples

* [example-frontend-js](example-frontend-js) -- frontend application written in Kotlin/JS
that uses coroutines to implement animations in imperative style.
