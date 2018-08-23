# kotlinx.coroutines 

[![official JetBrains project](http://jb.gg/badges/official.svg)](https://confluence.jetbrains.com/display/ALL/JetBrains+on+GitHub)
[![GitHub license](https://img.shields.io/badge/license-Apache%20License%202.0-blue.svg?style=flat)](http://www.apache.org/licenses/LICENSE-2.0)
[![Download](https://api.bintray.com/packages/kotlin/kotlinx/kotlinx.coroutines/images/download.svg?version=0.24.0) ](https://bintray.com/kotlin/kotlinx/kotlinx.coroutines/0.24.0)

Library support for Kotlin coroutines with [multiplatform](#multiplatform) support.
This is a companion version for Kotlin 1.2.61 release.

```kotlin
launch {
    delay(1000)
    println("Hello from Kotlin Coroutines!")
}
```

## Modules

* [common](common/README.md) &mdash; common coroutines across all backends:
  * `launch` and `async` coroutine builders;
  * `Job` and `Deferred` light-weight future with cancellation support;
  * `delay` and `yield` top-level suspending functions.
* [core](core/README.md) &mdash; Kotlin/JVM implementation of common coroutines with additional features:
  * `CommonPool` coroutine context (default on JVM);
  * `Channel` and `Mutex` communication and synchronization primitives;
  * `produce` and `actor` coroutine builders;
  * `select` expression support and more.
* [js](js/README.md) &mdash; Kotlin/JS implementation of common coroutines with `Promise` support.
* [native](native/README.md) &mdash; Kotlin/Native implementation of common coroutines with `runBlocking` single-threaded event loop.
* [reactive](reactive/README.md) &mdash; modules that provide builders and iteration support for various reactive streams libraries:
  * Reactive Streams, RxJava 1.x and 2.x and Project Reactor. 
* [ui](ui/README.md) &mdash; modules that provide coroutine dispatchers for various single-threaded UI libraries:
  * Android, JavaFX, and Swing.
* [integration](integration/README.md) &mdash; modules that provide integration with various asynchronous callback- and future-based libraries.
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
    <version>0.24.0</version>
</dependency>
```

And make sure that you use the latest Kotlin version:

```xml
<properties>
    <kotlin.version>1.2.61</kotlin.version>
</properties>
```

### Gradle

Add dependencies (you can also add other modules that you need):

```groovy
implementation 'org.jetbrains.kotlinx:kotlinx-coroutines-core:0.24.0'
```

And make sure that you use the latest Kotlin version:

```groovy
buildscript {
    ext.kotlin_version = '1.2.61'
}
```

Make sure that you have either `jcenter()` or `mavenCentral()` in the list of repositories:

```
repository {
    jcenter()
}
```

### Multiplatform

Core modules of `kotlinx.coroutines` are also available for 
[Kotlin/JS](js/README.md) and [Kotlin/Native](native/README.md). If you write
a common code that should get compiled or different platforms, add 
[`org.jetbrains.kotlinx:kotlinx-coroutines-core-common:<version>`](common/kotlinx-coroutines-core-common/README.md) 
to your common code dependencies.

### Android

Add [`kotlinx-coroutines-android`](ui/kotlinx-coroutines-android)
module as dependency when using `kotlinx.coroutines` on Android:

```groovy
implementation 'org.jetbrains.kotlinx:kotlinx-coroutines-android:0.24.0'
```

This gives you access to Android [UI](https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-android/kotlinx.coroutines.experimental.android/-u-i.html)
coroutine dispatcher and also makes sure that in case of crashed coroutine with unhandled exception this
exception is logged before crashing Android application, similarly to the way uncaught exceptions in 
threads are handled by Android runtime. 

### ProGuard

In obfuscated code, fields with different types can have the same names,
and `AtomicReferenceFieldUpdater` may be unable to find the correct ones.
To avoid field overloading by type during obfuscation, add this to your config:

```
-keepclassmembernames class kotlinx.** {
    volatile <fields>;
}
```

## Building 

This library is built with Gradle. To build it, use `./gradlew build`. 
You can import this project into IDEA, but you have to delegate build actions
to Gradle (in Preferences -> Build, Execution, Deployment -> Build Tools -> Gradle -> Runner)

### Requirements

* JDK >= 1.8 referred to by the `JAVA_HOME` environment variable.
* JDK 1.6 referred to by the `JDK_16` environment variable.

## Contributions and releases

All development (both new features and bug fixes) is performed in `develop` branch. 
This way `master` sources always contain sources of the most recently released version.
Please send PRs with bug fixes to `develop` branch.
Fixes to documentation in markdown files are an exception to this rule. They are updated directly in `master`.
                                                                          
The `develop` branch is pushed to `master` during release.

* Full release procedure checklist is [here](RELEASE.md).
* Steps for contributing new integration modules are explained [here](integration/README.md#Contributing).

