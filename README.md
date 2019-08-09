# kotlinx.coroutines 

[![official JetBrains project](https://jb.gg/badges/official.svg)](https://confluence.jetbrains.com/display/ALL/JetBrains+on+GitHub)
[![GitHub license](https://img.shields.io/badge/license-Apache%20License%202.0-blue.svg?style=flat)](https://www.apache.org/licenses/LICENSE-2.0)
[![Download](https://api.bintray.com/packages/kotlin/kotlinx/kotlinx.coroutines/images/download.svg?version=1.3.0-RC2) ](https://bintray.com/kotlin/kotlinx/kotlinx.coroutines/1.3.0-RC2)

Library support for Kotlin coroutines with [multiplatform](#multiplatform) support.
This is a companion version for Kotlin `1.3.41` release.

```kotlin
suspend fun main() = coroutineScope {
    launch { 
       delay(1000)
       println("Kotlin Coroutines World!") 
    }
    println("Hello")
}
```

> Play with coroutines online [here](https://pl.kotl.in/hG_tKbid_)

## Modules

* [core](kotlinx-coroutines-core/README.md) &mdash; common coroutines across all platforms:
  * `launch` and `async` coroutine builders;
  * `Job` and `Deferred` light-weight future with cancellation support;
  * `MainScope` for Android and UI applications.
  * `Dispatchers` object with `Main` dispatcher for Android/Swing/JavaFx, and `Default` dispatcher for background coroutines;
  * `delay` and `yield` top-level suspending functions;
  * `Channel` and `Mutex` communication and synchronization primitives;
  * `coroutineScope` and `supervisorScope` scope builders;
  * `SupervisorJob` and `CoroutineExceptionHandler` for supervision of coroutines hierarchies;
  * `select` expression support and more.
* [core/jvm](kotlinx-coroutines-core/jvm/) &mdash; additional core features available on Kotlin/JVM:
  * `Dispatchers.IO` dispatcher for blocking coroutines;
  * `Executor.asCoroutineDispatcher()` extension, custom thread pools, and more.
* [core/js](kotlinx-coroutines-core/js/) &mdash; additional core features available on Kotlin/JS:
  * Integration with `Promise`;
  * Integration with `Window`.
* [test](kotlinx-coroutines-test/README.md) &mdash; test utilities for coroutines
  * `Dispatchers.setMain` to override `Dispatchers.Main` in tests.
  * `TestCoroutineScope` to test suspending functions and coroutines.
* [debug](kotlinx-coroutines-debug/README.md) &mdash; debug utilities for coroutines.
  * `DebugProbes` API to probe, keep track of, print and dump active coroutines.
  * `CoroutinesTimeout` test rule to automatically dump coroutines on test timeout.
* [reactive](reactive/README.md) &mdash; modules that provide builders and iteration support for various reactive streams libraries:
  * Reactive Streams, RxJava 2.x, and Project Reactor. 
* [ui](ui/README.md) &mdash; modules that provide coroutine dispatchers for various single-threaded UI libraries:
  * Android, JavaFX, and Swing.
* [integration](integration/README.md) &mdash; modules that provide integration with various asynchronous callback- and future-based libraries.
  * JDK8 `CompletableFuture`, Guava `ListenableFuture`, and Google Play Services `Task`;
  * SLF4J MDC integration via `MDCContext`.

## Documentation

* Presentations and videos:
  * [Introduction to Coroutines](https://www.youtube.com/watch?v=_hfBv0a09Jc) (Roman Elizarov at KotlinConf 2017, [slides](https://www.slideshare.net/elizarov/introduction-to-coroutines-kotlinconf-2017))
  * [Deep dive into Coroutines](https://www.youtube.com/watch?v=YrrUCSi72E8) (Roman Elizarov at KotlinConf 2017, [slides](https://www.slideshare.net/elizarov/deep-dive-into-coroutines-on-jvm-kotlinconf-2017))
  * [Kotlin Coroutines in Practice](https://www.youtube.com/watch?v=a3agLJQ6vt8) (Roman Elizarov at KotlinConf 2018, [slides](https://www.slideshare.net/elizarov/kotlin-coroutines-in-practice-kotlinconf-2018))
* Guides and manuals: 
  * [Guide to kotlinx.coroutines by example](https://kotlinlang.org/docs/reference/coroutines/coroutines-guide.html) (**read it first**)
  * [Guide to UI programming with coroutines](ui/coroutines-guide-ui.md)
  * [Guide to reactive streams with coroutines](reactive/coroutines-guide-reactive.md)
  * [Debugging capabilities in kotlinx.coroutines](docs/debugging.md)
* [Compatibility policy and experimental annotations](docs/compatibility.md)
* [Change log for kotlinx.coroutines](CHANGES.md)
* [Coroutines design document (KEEP)](https://github.com/Kotlin/KEEP/blob/master/proposals/coroutines.md)
* [Full kotlinx.coroutines API reference](https://kotlin.github.io/kotlinx.coroutines)
 
## Using in your projects

The libraries are published to [kotlinx](https://bintray.com/kotlin/kotlinx/kotlinx.coroutines) bintray repository,
linked to [JCenter](https://bintray.com/bintray/jcenter?filterByPkgName=kotlinx.coroutines) and 
pushed to [Maven Central](https://search.maven.org/#search%7Cga%7C1%7Cg%3Aorg.jetbrains.kotlinx%20a%3Akotlinx-coroutines*).

### Maven

Add dependencies (you can also add other modules that you need):

```xml
<dependency>
    <groupId>org.jetbrains.kotlinx</groupId>
    <artifactId>kotlinx-coroutines-core</artifactId>
    <version>1.3.0-RC2</version>
</dependency>
```

And make sure that you use the latest Kotlin version:

```xml
<properties>
    <kotlin.version>1.3.41</kotlin.version>
</properties>
```

### Gradle

Add dependencies (you can also add other modules that you need):

```groovy
dependencies {
    implementation 'org.jetbrains.kotlinx:kotlinx-coroutines-core:1.3.0-RC2'
}
```

And make sure that you use the latest Kotlin version:

```groovy
buildscript {
    ext.kotlin_version = '1.3.41'
}
```

Make sure that you have either `jcenter()` or `mavenCentral()` in the list of repositories:

```
repository {
    jcenter()
}
```

### Gradle Kotlin DSL

Add dependencies (you can also add other modules that you need):

```groovy
dependencies {
    implementation("org.jetbrains.kotlinx:kotlinx-coroutines-core:1.3.0-RC2")
}
```

And make sure that you use the latest Kotlin version:

```groovy
plugins {
    kotlin("jvm") version "1.3.41"
}
```

Make sure that you have either `jcenter()` or `mavenCentral()` in the list of repositories.

### Multiplatform

Core modules of `kotlinx.coroutines` are also available for 
[Kotlin/JS](#js) and [Kotlin/Native](#native).
In common code that should get compiled for different platforms, add dependency to  
[`kotlinx-coroutines-core-common`](https://search.maven.org/artifact/org.jetbrains.kotlinx/kotlinx-coroutines-core-common/1.3.0-RC2/jar)
(follow the link to get the dependency declaration snippet).

### Android

Add [`kotlinx-coroutines-android`](ui/kotlinx-coroutines-android)
module as dependency when using `kotlinx.coroutines` on Android:

```groovy
implementation 'org.jetbrains.kotlinx:kotlinx-coroutines-android:1.3.0-RC2'
```

This gives you access to Android [Dispatchers.Main](https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-android/kotlinx.coroutines.android/kotlinx.coroutines.-dispatchers/index.html)
coroutine dispatcher and also makes sure that in case of crashed coroutine with unhandled exception this
exception is logged before crashing Android application, similarly to the way uncaught exceptions in 
threads are handled by Android runtime. 

#### R8 and ProGuard

For R8 no actions required, it will take obfuscation rules from the jar.

For Proguard  you need to add options from [coroutines.pro](kotlinx-coroutines-core/jvm/resources/META-INF/proguard/coroutines.pro) to your rules manually.
 
R8 is a replacement for ProGuard in Android ecosystem, it is enabled by default since Android gradle plugin 3.4.0 (3.3.0-beta also had it enabled).

### JS

[Kotlin/JS](https://kotlinlang.org/docs/reference/js-overview.html) version of `kotlinx.coroutines` is published as 
[`kotlinx-coroutines-core-js`](https://search.maven.org/artifact/org.jetbrains.kotlinx/kotlinx-coroutines-core-js/1.3.0-RC2/jar)
(follow the link to get the dependency declaration snippet).
 
You can also use [`kotlinx-coroutines-core`](https://www.npmjs.com/package/kotlinx-coroutines-core) package via NPM. 

### Native

[Kotlin/Native](https://kotlinlang.org/docs/reference/native-overview.html) version of `kotlinx.coroutines` is published as 
[`kotlinx-coroutines-core-native`](https://search.maven.org/artifact/org.jetbrains.kotlinx/kotlinx-coroutines-core-native/1.3.0-RC2/jar)
(follow the link to get the dependency declaration snippet).

Only single-threaded code (JS-style) on Kotlin/Native is currently supported. 
Kotlin/Native supports only Gradle version 4.10 and you need to enable Gradle metadata in your
`settings.gradle` file:

```groovy
enableFeaturePreview('GRADLE_METADATA')
```

Since Kotlin/Native does not generally provide binary compatibility between versions, 
you should use the same version of Kotlin/Native compiler as was used to build `kotlinx.coroutines`. 

## Building 

This library is built with Gradle. To build it, use `./gradlew build`. 
You can import this project into IDEA, but you have to delegate build actions
to Gradle (in Preferences -> Build, Execution, Deployment -> Build Tools -> Gradle -> Runner)

### Requirements

* JDK >= 1.8 referred to by the `JAVA_HOME` environment variable.
* JDK 1.6 referred to by the `JDK_16` environment variable. It is okay to have `JDK_16` pointing to `JAVA_HOME` for external contributions.

## Contributions and releases

All development (both new features and bug fixes) is performed in `develop` branch. 
This way `master` sources always contain sources of the most recently released version.
Please send PRs with bug fixes to `develop` branch.
Fixes to documentation in markdown files are an exception to this rule. They are updated directly in `master`.
                                                                          
The `develop` branch is pushed to `master` during release.

* Full release procedure checklist is [here](RELEASE.md).
* Steps for contributing new integration modules are explained [here](integration/README.md#Contributing).

