<!--- TOC -->

* [Compatibility](#compatibility)
* [Public API types](#public-api-types)
  * [Experimental API](#experimental-api)
  * [Flow preview API](#flow-preview-api)
  * [Obsolete API](#obsolete-api)
  * [Internal API](#internal-api)
  * [Stable API](#stable-api)
  * [Deprecation cycle](#deprecation-cycle)
* [Using annotated API](#using-annotated-api)
  * [Programmatically](#programmatically)
  * [Gradle](#gradle)
  * [Maven](#maven)

<!--- END -->

## Compatibility
This document describes the compatibility policy of `kotlinx.coroutines` library since version 1.0.0 and semantics of compatibility-specific annotations.


## Public API types
`kotlinx.coroutines` public API comes in five flavours: stable, experimental, obsolete, internal and deprecated. 
All public API except stable is marked with the corresponding annotation.

### Experimental API
Experimental API is marked with [@ExperimentalCoroutinesApi][ExperimentalCoroutinesApi] annotation.
API is marked experimental when its design has potential open questions which may eventually lead to 
either semantics changes of the API or its deprecation.

By default, most of the new API is marked as experimental and becomes stable in one of the next major releases if no new issues arise.
Otherwise, either semantics is fixed without changes in ABI or API goes through deprecation cycle. 

When using experimental API may be dangerous:
* You are writing a library which depends on `kotlinx.coroutines` and want to use experimental coroutines API in a stable library API.
It may lead to undesired consequences when end users of your library update their `kotlinx.coroutines` version where experimental API
has slightly different semantics.
* You want to build core infrastructure of the application around experimental API. 

### Flow preview API
All [Flow]-related API is marked with [@FlowPreview][FlowPreview] annotation.
This annotation indicates that Flow API is in preview status.
We provide no compatibility guarantees between releases for preview features, including binary, source and semantics compatibility.

When using preview API may be dangerous:
* You are writing a library/framework and want to use [Flow] API in a stable release or in a stable API.
* You want to use [Flow] in the core infrastructure of your application.
* You want to use [Flow] as "write-and-forget" solution and cannot afford additional maintenance cost when 
  it comes to `kotlinx.coroutines` updates.


### Obsolete API
Obsolete API is marked with [@ObsoleteCoroutinesApi][ObsoleteCoroutinesApi] annotation.
Obsolete API is similar to experimental, but already known to have serious design flaws and its potential replacement, 
but replacement is not yet implemented.

The semantics of this API won't be changed, but it will go through a deprecation cycle as soon as the replacement is ready.

### Internal API
Internal API is marked with [@InternalCoroutinesApi][InternalCoroutinesApi] or is part of `kotlinx.coroutines.internal` package.
This API has no guarantees on its stability, can and will be changed and/or removed in the future releases. 
If you can't avoid using internal API, please report it to [issue tracker](https://github.com/Kotlin/kotlinx.coroutines/issues/new).

### Stable API
Stable API is guaranteed to preserve its ABI and documented semantics. If at some point unfixable design flaws will be discovered, 
this API will go through a deprecation cycle and remain binary compatible as long as possible.

### Deprecation cycle
When some API is deprecated, it goes through multiple stages and there is at least one major release between stages.
* Feature is deprecated with compilation warning. Most of the time, proper replacement 
(and corresponding `replaceWith` declaration) is provided to automatically migrate deprecated usages with a help of IntelliJ IDEA.
* Deprecation level is increased to `error` or `hidden`. It is no longer possible to compile new code against deprecated API, 
  though it is still present in the ABI.
* API is completely removed. While we give our best efforts not to do so and have no plans of removing any API, we still are leaving 
this option in case of unforeseen problems such as security holes.

## Using annotated API
All API annotations are [kotlin.Experimental](https://kotlinlang.org/api/latest/jvm/stdlib/kotlin/-experimental/index.html).
It is done in order to produce compilation warning about using experimental or obsolete API.
Warnings can be disabled either programmatically for a specific call site or globally for the whole module.

### Programmatically
For a specific call-site, warning can be disabled by using [OptIn](https://kotlinlang.org/api/latest/jvm/stdlib/kotlin/-opt-in/) annotation:
```kotlin
@OptIn(ExperimentalCoroutinesApi::class) // Disables warning about experimental coroutines API 
fun experimentalApiUsage() {
    someKotlinxCoroutinesExperimentalMethod()
}
``` 

### Gradle
For the Gradle project, a warning can be disabled by passing a compiler flag in your `build.gradle` file:

```groovy
tasks.withType(org.jetbrains.kotlin.gradle.tasks.AbstractKotlinCompile).all {
    kotlinOptions.freeCompilerArgs += ["-Xuse-experimental=kotlinx.coroutines.ExperimentalCoroutinesApi"]
}

```

### Maven
For the Maven project, a warning can be disabled by passing a compiler flag in your `pom.xml` file:
```xml
<plugin>
    <artifactId>kotlin-maven-plugin</artifactId>
    <groupId>org.jetbrains.kotlin</groupId>
    ... your configuration ...
    <configuration>
        <args>
            <arg>-Xuse-experimental=kotlinx.coroutines.ExperimentalCoroutinesApi</arg>
        </args>
    </configuration>
</plugin>
```


<!--- MODULE kotlinx-coroutines-core -->
<!--- INDEX kotlinx.coroutines.flow -->

[Flow]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/-flow/index.html

<!--- INDEX kotlinx.coroutines -->

[ExperimentalCoroutinesApi]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-experimental-coroutines-api/index.html
[FlowPreview]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-flow-preview/index.html
[ObsoleteCoroutinesApi]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-obsolete-coroutines-api/index.html
[InternalCoroutinesApi]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-internal-coroutines-api/index.html

<!--- END -->
