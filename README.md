# kotlinx.coroutines

Library support for Kotlin coroutines. This is a companion version for Kotlin 1.1.0-beta-37 release. 

## Modules and features

* `kotlinx-coroutines-core` module with core primitives to work with coroutines. It is designed to work on any JDK6+ and Android
and contains the following main pieces:
  * `launch(context) {...}` to start a coroutine in the given context and get reference to its `Job`.
  * `run(context) {...}` to switch to a different context inside a coroutine.
  * `runBlocking {...}` to use asynchronous Kotlin APIs from a thread-blocking code.  
  * `defer(context) {...}` and `lazyDefer(context) {...}` to get a deferred result of coroutine execution in a 
     non-blocking way via a light-weight future interface called `Deferred`.
  * `delay(...)` for a non-blocking sleep in coroutines and `yield` to release a thread in single-threaded dispatchers.
  * `withTimeout(timeout) {...}` scope function to easily set coroutine time-limit (deadline),
     and `NonCancellable` context to avoid it when needed.
  * `CommonPool` and `Here` contexts, access to `context` of a parent coroutine in its `CoroutineScope`.
  * `newSingleThreadContext(...)` and `newFixedThreadPoolContext(...)` functions, 
    `Executor.toCoroutineDispatcher()` extension.
  * Cancellation support with `Job` interface and `suspendCancellableCoroutine` helper function.
  * Debugging facilities for coroutines (run JVM with `-ea` or `-Dkotlinx.coroutines.debug` options) and
    `newCoroutineContext(context)` function to write user-defined coroutine builders that work with these
     debugging facilities.
 
* `kotlinx-coroutines-jdk8` module with additional libraries for JDK8 (or Android API level 24).
  * `future { ... }` coroutine builder that returns `CompletableFuture` and works in `CommonPool` context by default.
  * `.await()` suspending function for `CompletableFuture`.

* `kotlinx-coroutines-nio` module with extensions for asynchronous IO on JDK7+.

* `kotlinx-coroutines-swing` module with `Swing` context for Swing UI applications.

* `kotlinx-coroutines-javafx` module with `JavaFx` context for JavaFX UI applications.

* `kotlinx-coroutines-rx` module with utilities to build `Observable` objects from
[RxJava](https://github.com/ReactiveX/RxJava) with imperative coroutines and consume their values 
from inside coroutines. It is in very basic form now (example-only, not even close to production use)

## References and documentation

* [Guide to kotlinx.coroutines by example](coroutines-guide.md) 
* [Change log for kotlinx.coroutines](CHANGES.md)
* [Coroutines design document (KEEP)](https://github.com/Kotlin/kotlin-coroutines/blob/master/kotlin-coroutines-informal.md)
 
## Using in your projects

> Note that these libraries are experimental and are subject to change.

The libraries are published to [kotlin-eap-1.1](https://bintray.com/kotlin/kotlin-eap-1.1/kotlinx.coroutines) bintray repository.

These libraries require kotlin compiler version to be at least `1.1.0-beta-37` and 
require kotlin runtime of the same version as a dependency, which can be obtained from the same repository.

### Maven

Add the bintray repository to `<repositories>` section (and also add `pluginRepository` to `<pluginRepositories>`,
if you're willing to get `kotlin-maven-plugin` from there):

```xml
<repository>
    <snapshots>
        <enabled>false</enabled>
    </snapshots>
    <id>dl</id>
    <name>bintray</name>
    <url>http://dl.bintray.com/kotlin/kotlin-eap-1.1</url>
</repository>
```

Add dependencies (you can also add other modules that you need):

```xml
<dependency>
    <groupId>org.jetbrains.kotlinx</groupId>
    <artifactId>kotlinx-coroutines-core</artifactId>
    <version>0.6-beta</version>
</dependency>
```

And make sure that you use the right Kotlin version:

```xml
<properties>
    <kotlin.version>1.1.0-beta-37</kotlin.version>
</properties>
```

### Gradle

Add the bintray repository (and also add it to `buildScript` section, if you're willing to get `kotlin-gradle-plugin` from there):

```groovy
repositories {
    maven {
        url "http://dl.bintray.com/kotlin/kotlin-eap-1.1"
    }
}
```

Add dependencies (you can also add other modules that you need):

```groovy
compile 'org.jetbrains.kotlinx:kotlinx-coroutines-core:0.6-beta'
```

And make sure that you use the right Kotlin version:

```groovy
buildscript {
    ext.kotlin_version = '1.1.0-beta-37'
}
```
