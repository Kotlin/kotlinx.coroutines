# kotlinx.coroutines

Library support for Kotlin coroutines. This is a companion version for Kotlin 1.1.0-rc-69 release. 

## Modules and features

* [kotlinx-coroutines-core](kotlinx-coroutines-core) module with core primitives to work with coroutines. 
  * This module's functionality is covered by the [guide to kotlinx.coroutines](coroutines-guide.md). 
* [kotlinx-coroutines-jdk8](kotlinx-coroutines-jdk8) module with additional libraries for JDK8 (or Android API level 24).
* [kotlinx-coroutines-nio](kotlinx-coroutines-nio) module with extensions for asynchronous IO on JDK7+.
* [kotlinx-coroutines-swing](kotlinx-coroutines-swing) module with `Swing` context for Swing UI applications.
* [kotlinx-coroutines-javafx](kotlinx-coroutines-javafx) module with `JavaFx` context for JavaFX UI applications.
* [kotlinx-coroutines-rx](kotlinx-coroutines-rx) module with utilities for [RxJava](https://github.com/ReactiveX/RxJava).
 
## References and documentation

* [Guide to kotlinx.coroutines by example](coroutines-guide.md) 
* [Change log for kotlinx.coroutines](CHANGES.md)
* [Coroutines design document (KEEP)](https://github.com/Kotlin/kotlin-coroutines/blob/master/kotlin-coroutines-informal.md)
 
## Using in your projects

> Note that these libraries are experimental and are subject to change.

The libraries are published to [kotlin-eap-1.1](https://bintray.com/kotlin/kotlin-eap-1.1/kotlinx.coroutines) bintray repository.

These libraries require kotlin compiler version to be at least `1.1.0-rc-69` and 
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
    <version>0.9-rc</version>
</dependency>
```

And make sure that you use the right Kotlin version:

```xml
<properties>
    <kotlin.version>1.1.0-rc-69</kotlin.version>
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
compile 'org.jetbrains.kotlinx:kotlinx-coroutines-core:0.9-rc'
```

And make sure that you use the right Kotlin version:

```groovy
buildscript {
    ext.kotlin_version = '1.1.0-rc-69'
}
```
