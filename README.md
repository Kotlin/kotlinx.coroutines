# kotlinx.coroutines [ ![Download](https://api.bintray.com/packages/kotlin/kotlinx/kotlinx.coroutines/images/download.svg) ](https://bintray.com/kotlin/kotlinx/kotlinx.coroutines/_latestVersion)

Library support for Kotlin coroutines. This is a companion version for Kotlin 1.1 release. 

## Modules

Core module:

* [kotlinx-coroutines-core](kotlinx-coroutines-core) -- core primitives to work with coroutines.

Modules that provide builders and iteration support for various reactive streams libraries:

* [kotlinx-coroutines-reactive](reactive/kotlinx-coroutines-reactive) -- utilities for [Reactive Streams](http://www.reactive-streams.org)
* [kotlinx-coroutines-reactor](reactive/kotlinx-coroutines-reactor) -- utilities for [Reactor](https://projectreactor.io)
* [kotlinx-coroutines-rx1](reactive/kotlinx-coroutines-rx1) -- utilities for [RxJava 1.x](https://github.com/ReactiveX/RxJava/tree/1.x)
* [kotlinx-coroutines-rx2](reactive/kotlinx-coroutines-rx2) -- utilities for [RxJava 2.x](https://github.com/ReactiveX/RxJava)

Modules that provide coroutine dispatchers for various single-threaded UI libraries:

* [kotlinx-coroutines-android](ui/kotlinx-coroutines-android) -- `UI` context for Android applications.
* [kotlinx-coroutines-javafx](ui/kotlinx-coroutines-javafx) -- `JavaFx` context for JavaFX UI applications.
* [kotlinx-coroutines-swing](ui/kotlinx-coroutines-swing) -- `Swing` context for Swing UI applications.

Modules that provide integration with various asynchronous callback- and future-based libraries:
 
* [kotlinx-coroutines-jdk8](integration/kotlinx-coroutines-jdk8) -- extensions for JDK8 `CompletableFuture` (Android API level 24).
* [kotlinx-coroutines-nio](integration/kotlinx-coroutines-nio) -- extensions for asynchronous IO on JDK7+ (Android O Preview).

## Documentation

* [Guide to kotlinx.coroutines by example](coroutines-guide.md) (**read it first**)
* [Guide to UI programming with coroutines](ui/coroutines-guide-ui.md)
* [Guide to reactive streams with coroutines](reactive/coroutines-guide-reactive.md)
* [Change log for kotlinx.coroutines](CHANGES.md)
* [Coroutines design document (KEEP)](https://github.com/Kotlin/kotlin-coroutines/blob/master/kotlin-coroutines-informal.md)
* [Full kotlinx.coroutines API reference](http://kotlin.github.io/kotlinx.coroutines)
 
## Using in your projects

> Note that these libraries are experimental and are subject to change.

The libraries are published to [kotlinx](https://bintray.com/kotlin/kotlinx/kotlinx.coroutines) bintray repository
and also linked to [JCenter](https://bintray.com/bintray/jcenter?filterByPkgName=kotlinx.coroutines).

These libraries require kotlin compiler version `1.1.x` and 
require kotlin runtime of the same version as a dependency.

### Maven

Add Bintray JCenter repository to `<repositories>` section:

```xml
<repository>
    <id>central</id>
    <url>http://jcenter.bintray.com</url>
</repository>
```

Add dependencies (you can also add other modules that you need):

```xml
<dependency>
    <groupId>org.jetbrains.kotlinx</groupId>
    <artifactId>kotlinx-coroutines-core</artifactId>
    <version>0.16</version>
</dependency>
```

And make sure that you use the right Kotlin version:

```xml
<properties>
    <kotlin.version>1.1.2</kotlin.version>
</properties>
```

### Gradle

Add Bintray JCenter repository:

```groovy
repositories {
    jcenter()
}
```

Add dependencies (you can also add other modules that you need):

```groovy
compile 'org.jetbrains.kotlinx:kotlinx-coroutines-core:0.16'
```

And make sure that you use the right Kotlin version:

```groovy
buildscript {
    ext.kotlin_version = '1.1.2'
}
```
