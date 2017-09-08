# kotlinx.coroutines 

[![official JetBrains project](http://jb.gg/badges/official.svg)](https://confluence.jetbrains.com/display/ALL/JetBrains+on+GitHub)
[![GitHub license](https://img.shields.io/badge/license-Apache%20License%202.0-blue.svg?style=flat)](http://www.apache.org/licenses/LICENSE-2.0)
[![Download](https://api.bintray.com/packages/kotlin/kotlinx/kotlinx.coroutines/images/download.svg?version=0.18) ](https://bintray.com/kotlin/kotlinx/kotlinx.coroutines/0.18)

Library support for Kotlin coroutines. 
This is a companion version for Kotlin 1.1.4 release (this is the minimal required Kotlin runtime version). 

## Modules

* [core](core/README.md) -- core primitives to work with coroutines:
  * `launch`, `async`, `produce`, `actor`, etc coroutine builders;
  * `Job` and `Deferred` light-weight future with cancellation support;
  * `CommonPool` and other coroutine contexts;
  * `Channel` and `Mutex` communication and synchronization primitives;
  * `delay`, `yield`, etc top-level suspending functions;
  * `select` expression support and more.
* [reactive](reactive/README.md) -- modules that provide builders and iteration support for various reactive streams libraries:
  * Reactive Streams, RxJava 1.x and 2.x and Project Reactor. 
* [ui](ui/README.md) -- modules that provide coroutine dispatchers for various single-threaded UI libraries:
  * Android, JavaFx, and Swing.
* [integration](integration/README.md) -- modules that provide integration with various asynchronous callback- and future-based libraries.
  * JDK8 `CompletableFuture`, Guava `ListenableFuture`, and synchronous networking/IO.

## Documentation

* [Introduction to Kotlin Coroutines](https://vimeo.com/222499934) video
  (Roman Elizarov at GeekOut 2017, [slides](https://www.slideshare.net/elizarov/introduction-to-kotlin-coroutines))
* Guides and manuals: 
  * [Guide to kotlinx.coroutines by example](coroutines-guide.md) (**read it first**)
  * [Guide to UI programming with coroutines](ui/coroutines-guide-ui.md)
  * [Guide to reactive streams with coroutines](reactive/coroutines-guide-reactive.md)
* [Change log for kotlinx.coroutines](CHANGES.md)
* [Coroutines design document (KEEP)](https://github.com/Kotlin/kotlin-coroutines/blob/master/kotlin-coroutines-informal.md)
* [Full kotlinx.coroutines API reference](http://kotlin.github.io/kotlinx.coroutines)
 
## Using in your projects

> Note that these libraries are experimental and are subject to change.

The libraries are published to [kotlinx](https://bintray.com/kotlin/kotlinx/kotlinx.coroutines) bintray repository,
linked to [JCenter](https://bintray.com/bintray/jcenter?filterByPkgName=kotlinx.coroutines) and 
pushed to [Maven Central](https://search.maven.org/#search%7Cga%7C1%7Cg%3Aorg.jetbrains.kotlinx%20a%3Akotlinx-coroutines).

These libraries require kotlin compiler version `1.1.4` or later and 
require kotlin runtime of the same version as a dependency.

### Maven

Add dependencies (you can also add other modules that you need):

```xml
<dependency>
    <groupId>org.jetbrains.kotlinx</groupId>
    <artifactId>kotlinx-coroutines-core</artifactId>
    <version>0.18</version>
</dependency>
```

And make sure that you use the right Kotlin version:

```xml
<properties>
    <kotlin.version>1.1.4</kotlin.version>
</properties>
```

### Gradle

Add dependencies (you can also add other modules that you need):

```groovy
compile 'org.jetbrains.kotlinx:kotlinx-coroutines-core:0.18'
```

And make sure that you use the right Kotlin version:

```groovy
buildscript {
    ext.kotlin_version = '1.1.4'
}
```

### ProGuard

In obfuscated code, fields with different types can have the same names,
and `AtomicReferenceFieldUpdater` may be unable to find the correct ones.
To avoid field overloading by type during obfuscation, add this to your config:
```
-keepclassmembernames class kotlinx.** {
    volatile <fields>;
}
```
