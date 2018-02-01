# kotlinx.coroutines 

[![official JetBrains project](http://jb.gg/badges/official.svg)](https://confluence.jetbrains.com/display/ALL/JetBrains+on+GitHub)
[![GitHub license](https://img.shields.io/badge/license-Apache%20License%202.0-blue.svg?style=flat)](http://www.apache.org/licenses/LICENSE-2.0)
[![Download](https://api.bintray.com/packages/kotlin/kotlinx/kotlinx.coroutines/images/download.svg?version=0.22.1) ](https://bintray.com/kotlin/kotlinx/kotlinx.coroutines/0.22.1)

Library support for Kotlin coroutines in
[Kotlin/JVM](core/README.md) and
[Kotlin/JS](js/README.md).
This is a companion version for Kotlin 1.2.21 release.

```kotlin
launch {
    delay(1000)
    println("Hello from Kotlin Coroutines!")
}
```

## Modules

* [common](common/README.md) - common coroutines across all backends:
  * `launch` and `async` coroutine builders;
  * `Job` and `Deferred` light-weight future with cancellation support;
  * `delay` and `yield` top-level suspending functions.
* [js](js/README.md) - Kotlin/JS implementation of common coroutines with `Promise` support.
* [core](core/README.md) -- Kotlin/JVM implementation of common coroutines with additional features:
  * `CommonPool` coroutine context (default on JVM);
  * `Channel` and `Mutex` communication and synchronization primitives;
  * `produce` and `actor` coroutine builders;
  * `select` expression support and more.
* [reactive](reactive/README.md) -- modules that provide builders and iteration support for various reactive streams libraries:
  * Reactive Streams, RxJava 1.x and 2.x and Project Reactor. 
* [ui](ui/README.md) -- modules that provide coroutine dispatchers for various single-threaded UI libraries:
  * Android, JavaFx, and Swing.
* [integration](integration/README.md) -- modules that provide integration with various asynchronous callback- and future-based libraries.
  * JDK8 `CompletableFuture`, Guava `ListenableFuture`, and synchronous networking/IO.

## Documentation

* Presentations and videos:
   * [Introduction to Coroutines](https://www.youtube.com/watch?v=_hfBv0a09Jc) (Roman Elizarov at KotlinConf 2017, [slides](https://www.slideshare.net/elizarov/introduction-to-coroutines-kotlinconf-2017))
   * [Deep dive into Coroutines](https://www.youtube.com/watch?v=YrrUCSi72E8) (Roman Elizarov at KotlinConf 2017, [slides](https://www.slideshare.net/elizarov/deep-dive-into-coroutines-on-jvm-kotlinconf-2017))
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
pushed to [Maven Central](https://search.maven.org/#search%7Cga%7C1%7Cg%3Aorg.jetbrains.kotlinx%20a%3Akotlinx-coroutines*).

### Maven

Add dependencies (you can also add other modules that you need):

```xml
<dependency>
    <groupId>org.jetbrains.kotlinx</groupId>
    <artifactId>kotlinx-coroutines-core</artifactId>
    <version>0.22.1</version>
</dependency>
```

And make sure that you use the latest Kotlin version:

```xml
<properties>
    <kotlin.version>1.2.21</kotlin.version>
</properties>
```

### Gradle

Add dependencies (you can also add other modules that you need):

```groovy
compile 'org.jetbrains.kotlinx:kotlinx-coroutines-core:0.22.1'
```

And make sure that you use the latest Kotlin version:

```groovy
buildscript {
    ext.kotlin_version = '1.2.21'
}
```

### Kotlin/JS

Use `kotlinx-coroutines-core-js` artifact in your dependencies.

### ProGuard

In obfuscated code, fields with different types can have the same names,
and `AtomicReferenceFieldUpdater` may be unable to find the correct ones.
To avoid field overloading by type during obfuscation, add this to your config:

```
-keepclassmembernames class kotlinx.** {
    volatile <fields>;
}
```

You also need to keep this class if you build your Android releases with `minifyEnabled true`:

```
-keep class kotlinx.coroutines.experimental.android.AndroidExceptionPreHandler
```
