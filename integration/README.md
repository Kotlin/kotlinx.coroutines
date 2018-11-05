# Coroutines integration

This directory contains modules that provide integration with various asynchronous callback- and future-based libraries.
Module name below corresponds to the artifact name in Maven/Gradle.

## Modules

* [kotlinx-coroutines-jdk8](kotlinx-coroutines-jdk8/README.md) -- integration with JDK8 `CompletableFuture` (Android API level 24).
* [kotlinx-coroutines-guava](kotlinx-coroutines-guava/README.md) -- integration with Guava [ListenableFuture](https://github.com/google/guava/wiki/ListenableFutureExplained).
* [kotlinx-coroutines-slf4j](kotlinx-coroutines-slf4j/README.md) -- integration with SLF4J [MDC](https://logback.qos.ch/manual/mdc.html).
* [kotlinx-coroutines-play-services](kotlinx-coroutines-play-services) -- integration with Google Play Services [Tasks API](https://developers.google.com/android/guides/tasks).

## Contributing

Follow the following simple guidelines when contributing integration with your favorite library:

* Keep it simple and general. Ideally it should fit into a single file. If it does not fit, then consider
  a separate GitHub project to host this integration.
* Follow the example of other modules. 
  Cut-and-paste [kotlinx-coroutines-guava](kotlinx-coroutines-guava) module as a template.
* Write tests and documentation, include top-level `README.md` with short overview and example.
* Reference the new module from all the places:
  * List of modules in this document.
  * List of modules in top-level [`settings.gradle`](../settings.gradle).
  * List of modules at the root of documentation site in [`site/docs/index.md`](../site/docs/index.md).
* Update links to documentation website as explained [here](../knit/README.md#usage).
* Squash your contribution to a single commit and create pull request to `develop` branch.
