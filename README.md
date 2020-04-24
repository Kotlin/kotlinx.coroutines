# kotlinx.coroutines 

[![official JetBrains project](https://jb.gg/badges/official.svg)](https://confluence.jetbrains.com/display/ALL/JetBrains+on+GitHub)
[![GitHub license](https://img.shields.io/badge/license-Apache%20License%202.0-blue.svg?style=flat)](https://www.apache.org/licenses/LICENSE-2.0)
[![Download](https://api.bintray.com/packages/kotlin/kotlinx/kotlinx.coroutines/images/download.svg?version=1.3.5) ](https://bintray.com/kotlin/kotlinx/kotlinx.coroutines/1.3.5)

Library support for Kotlin coroutines with [multiplatform](#multiplatform) support.
This is a companion version for Kotlin `1.3.71` release.

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
  * [launch] and [async] coroutine builders returning [Job] and [Deferred] light-weight futures with cancellation support;
  * [Dispatchers] object with [Main][Dispatchers.Main] dispatcher for Android/Swing/JavaFx, and [Default][Dispatchers.Default] dispatcher for background coroutines;
  * [delay] and [yield] top-level suspending functions;
  * [Flow] &mdash; cold asynchronous stream with [flow][_flow] builder and comprehensive operator set ([filter], [map], etc);
  * [Channel], [Mutex], and [Semaphore] communication and synchronization primitives;
  * [coroutineScope], [supervisorScope], [withContext], and [withTimeout] scope builders;
  * [MainScope()] for Android and UI applications;
  * [SupervisorJob()] and [CoroutineExceptionHandler] for supervision of coroutines hierarchies;
  * [select] expression support and more.
* [core/jvm](kotlinx-coroutines-core/jvm/) &mdash; additional core features available on Kotlin/JVM:
  * [Dispatchers.IO] dispatcher for blocking coroutines;
  * [Executor.asCoroutineDispatcher] extension, custom thread pools, and more.
* [core/js](kotlinx-coroutines-core/js/) &mdash; additional core features available on Kotlin/JS:
  * Integration with `Promise` via [Promise.await] and [promise] builder;
  * Integration with `Window` via [Window.asCoroutineDispatcher], etc.
* [test](kotlinx-coroutines-test/README.md) &mdash; test utilities for coroutines:
  * [Dispatchers.setMain] to override [Dispatchers.Main] in tests;
  * [TestCoroutineScope] to test suspending functions and coroutines.
* [debug](kotlinx-coroutines-debug/README.md) &mdash; debug utilities for coroutines:
  * [DebugProbes] API to probe, keep track of, print and dump active coroutines;
  * [CoroutinesTimeout] test rule to automatically dump coroutines on test timeout.
* [reactive](reactive/README.md) &mdash; modules that provide builders and iteration support for various reactive streams libraries:
  * Reactive Streams ([Publisher.collect], [Publisher.awaitSingle], [publish], etc), 
  * Flow (JDK 9) (the same interface as for Reactive Streams),
  * RxJava 2.x ([rxFlowable], [rxSingle], etc), and
  * RxJava 3.x ([rxFlowable], [rxSingle], etc), and
  * Project Reactor ([flux], [mono], etc).
* [ui](ui/README.md) &mdash; modules that provide coroutine dispatchers for various single-threaded UI libraries:
  * Android, JavaFX, and Swing.
* [integration](integration/README.md) &mdash; modules that provide integration with various asynchronous callback- and future-based libraries:
  * JDK8 [CompletionStage.await], Guava [ListenableFuture.await], and Google Play Services [Task.await];
  * SLF4J MDC integration via [MDCContext].

## Documentation

* Presentations and videos:
  * [Introduction to Coroutines](https://www.youtube.com/watch?v=_hfBv0a09Jc) (Roman Elizarov at KotlinConf 2017, [slides](https://www.slideshare.net/elizarov/introduction-to-coroutines-kotlinconf-2017))
  * [Deep dive into Coroutines](https://www.youtube.com/watch?v=YrrUCSi72E8) (Roman Elizarov at KotlinConf 2017, [slides](https://www.slideshare.net/elizarov/deep-dive-into-coroutines-on-jvm-kotlinconf-2017))
  * [Kotlin Coroutines in Practice](https://www.youtube.com/watch?v=a3agLJQ6vt8) (Roman Elizarov at KotlinConf 2018, [slides](https://www.slideshare.net/elizarov/kotlin-coroutines-in-practice-kotlinconf-2018))
* Guides and manuals: 
  * [Guide to kotlinx.coroutines by example](https://kotlinlang.org/docs/reference/coroutines/coroutines-guide.html) (**read it first**)
  * [Guide to UI programming with coroutines](ui/coroutines-guide-ui.md)
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
    <version>1.3.5</version>
</dependency>
```

And make sure that you use the latest Kotlin version:

```xml
<properties>
    <kotlin.version>1.3.71</kotlin.version>
</properties>
```

### Gradle

Add dependencies (you can also add other modules that you need):

```groovy
dependencies {
    implementation 'org.jetbrains.kotlinx:kotlinx-coroutines-core:1.3.5'
}
```

And make sure that you use the latest Kotlin version:

```groovy
buildscript {
    ext.kotlin_version = '1.3.71'
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
    implementation("org.jetbrains.kotlinx:kotlinx-coroutines-core:1.3.5")
}
```

And make sure that you use the latest Kotlin version:

```groovy
plugins {
    kotlin("jvm") version "1.3.71"
}
```

Make sure that you have either `jcenter()` or `mavenCentral()` in the list of repositories.

### Multiplatform

Core modules of `kotlinx.coroutines` are also available for 
[Kotlin/JS](#js) and [Kotlin/Native](#native).
In common code that should get compiled for different platforms, add dependency to  
[`kotlinx-coroutines-core-common`](https://search.maven.org/artifact/org.jetbrains.kotlinx/kotlinx-coroutines-core-common/1.3.5/jar)
(follow the link to get the dependency declaration snippet).

### Android

Add [`kotlinx-coroutines-android`](ui/kotlinx-coroutines-android)
module as dependency when using `kotlinx.coroutines` on Android:

```groovy
implementation 'org.jetbrains.kotlinx:kotlinx-coroutines-android:1.3.5'
```

This gives you access to Android [Dispatchers.Main]
coroutine dispatcher and also makes sure that in case of crashed coroutine with unhandled exception this
exception is logged before crashing Android application, similarly to the way uncaught exceptions in 
threads are handled by Android runtime. 

#### R8 and ProGuard

R8 and ProGuard rules are bundled into the [`kotlinx-coroutines-android`](ui/kotlinx-coroutines-android) module.
For more details see ["Optimization" section for Android](ui/kotlinx-coroutines-android/README.md#optimization). 

### JS

[Kotlin/JS](https://kotlinlang.org/docs/reference/js-overview.html) version of `kotlinx.coroutines` is published as 
[`kotlinx-coroutines-core-js`](https://search.maven.org/artifact/org.jetbrains.kotlinx/kotlinx-coroutines-core-js/1.3.5/jar)
(follow the link to get the dependency declaration snippet).
 
You can also use [`kotlinx-coroutines-core`](https://www.npmjs.com/package/kotlinx-coroutines-core) package via NPM. 

### Native

[Kotlin/Native](https://kotlinlang.org/docs/reference/native-overview.html) version of `kotlinx.coroutines` is published as 
[`kotlinx-coroutines-core-native`](https://search.maven.org/artifact/org.jetbrains.kotlinx/kotlinx-coroutines-core-native/1.3.5/jar)
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

* JDK >= 11 referred to by the `JAVA_HOME` environment variable.
* JDK 1.6 referred to by the `JDK_16` environment variable. It is okay to have `JDK_16` pointing to `JAVA_HOME` for external contributions.
* JDK 1.8 referred to by the `JDK_18` environment variable. Only used by nightly stress-tests. It is okay to have `JDK_18` pointing to `JAVA_HOME` for external contributions.

## Contributions and releases

All development (both new features and bug fixes) is performed in `develop` branch. 
This way `master` sources always contain sources of the most recently released version.
Please send PRs with bug fixes to `develop` branch.
Fixes to documentation in markdown files are an exception to this rule. They are updated directly in `master`.
                                                                          
The `develop` branch is pushed to `master` during release.

* Full release procedure checklist is [here](RELEASE.md).
* Steps for contributing new integration modules are explained [here](integration/README.md#Contributing).
* Use [Knit](https://github.com/Kotlin/kotlinx-knit/blob/master/README.md) for updates to documentation:
  * In project root directory run `./gradlew knit`.
  * Commit updated documents and examples together with other changes.
* Use [Binary Compatibility Validator](https://github.com/Kotlin/binary-compatibility-validator/blob/master/README.md) for updates to public API:
  * In project root directory run `./gradlew apiDump`. 
  * Commit updated API index together with other changes.

<!--- MODULE kotlinx-coroutines-core -->
<!--- INDEX kotlinx.coroutines -->
[launch]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/launch.html
[async]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/async.html
[Job]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-job/index.html
[Deferred]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-deferred/index.html
[Dispatchers]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-dispatchers/index.html
[Dispatchers.Main]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-dispatchers/-main.html
[Dispatchers.Default]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-dispatchers/-default.html
[delay]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/delay.html
[yield]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/yield.html
[coroutineScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/coroutine-scope.html
[supervisorScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/supervisor-scope.html
[withContext]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/with-context.html
[withTimeout]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/with-timeout.html
[MainScope()]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-main-scope.html
[SupervisorJob()]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-supervisor-job.html
[CoroutineExceptionHandler]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-coroutine-exception-handler/index.html
[Dispatchers.IO]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-dispatchers/-i-o.html
[Executor.asCoroutineDispatcher]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/java.util.concurrent.-executor/as-coroutine-dispatcher.html
[Promise.await]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/kotlin.js.-promise/await.html
[promise]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/promise.html
[Window.asCoroutineDispatcher]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/org.w3c.dom.-window/as-coroutine-dispatcher.html
<!--- INDEX kotlinx.coroutines.flow -->
[Flow]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/-flow/index.html
[_flow]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/flow.html
[filter]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/filter.html
[map]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/map.html
<!--- INDEX kotlinx.coroutines.channels -->
[Channel]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-channel/index.html
<!--- INDEX kotlinx.coroutines.selects -->
[select]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.selects/select.html
<!--- INDEX kotlinx.coroutines.sync -->
[Mutex]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.sync/-mutex/index.html
[Semaphore]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.sync/-semaphore/index.html
<!--- MODULE kotlinx-coroutines-test -->
<!--- INDEX kotlinx.coroutines.test -->
[Dispatchers.setMain]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-test/kotlinx.coroutines.test/kotlinx.coroutines.-dispatchers/set-main.html
[TestCoroutineScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-test/kotlinx.coroutines.test/-test-coroutine-scope/index.html
<!--- MODULE kotlinx-coroutines-debug -->
<!--- INDEX kotlinx.coroutines.debug -->
[DebugProbes]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-debug/kotlinx.coroutines.debug/-debug-probes/index.html
<!--- INDEX kotlinx.coroutines.debug.junit4 -->
[CoroutinesTimeout]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-debug/kotlinx.coroutines.debug.junit4/-coroutines-timeout/index.html
<!--- MODULE kotlinx-coroutines-slf4j -->
<!--- INDEX kotlinx.coroutines.slf4j -->
[MDCContext]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-slf4j/kotlinx.coroutines.slf4j/-m-d-c-context/index.html
<!--- MODULE kotlinx-coroutines-jdk8 -->
<!--- INDEX kotlinx.coroutines.future -->
[CompletionStage.await]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-jdk8/kotlinx.coroutines.future/java.util.concurrent.-completion-stage/await.html
<!--- MODULE kotlinx-coroutines-guava -->
<!--- INDEX kotlinx.coroutines.guava -->
[ListenableFuture.await]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-guava/kotlinx.coroutines.guava/com.google.common.util.concurrent.-listenable-future/await.html
<!--- MODULE kotlinx-coroutines-play-services -->
<!--- INDEX kotlinx.coroutines.tasks -->
[Task.await]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-play-services/kotlinx.coroutines.tasks/com.google.android.gms.tasks.-task/await.html
<!--- MODULE kotlinx-coroutines-reactive -->
<!--- INDEX kotlinx.coroutines.reactive -->
[Publisher.collect]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-reactive/kotlinx.coroutines.reactive/org.reactivestreams.-publisher/collect.html
[Publisher.awaitSingle]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-reactive/kotlinx.coroutines.reactive/org.reactivestreams.-publisher/await-single.html
[publish]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-reactive/kotlinx.coroutines.reactive/publish.html
<!--- MODULE kotlinx-coroutines-rx2 -->
<!--- INDEX kotlinx.coroutines.rx2 -->
[rxFlowable]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx2/kotlinx.coroutines.rx2/rx-flowable.html
[rxSingle]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-rx2/kotlinx.coroutines.rx2/rx-single.html
<!--- MODULE kotlinx-coroutines-rx2 -->
<!--- INDEX kotlinx.coroutines.rx2 -->
<!--- MODULE kotlinx-coroutines-reactor -->
<!--- INDEX kotlinx.coroutines.reactor -->
[flux]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-reactor/kotlinx.coroutines.reactor/flux.html
[mono]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-reactor/kotlinx.coroutines.reactor/mono.html
<!--- END -->
