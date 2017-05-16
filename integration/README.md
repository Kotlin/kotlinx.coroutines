# Coroutines for reactive streams

This directory contains modules that provide integration with various asynchronous callback- and future-based libraries:

## Modules

* [kotlinx-coroutines-jdk8](kotlinx-coroutines-jdk8/README.md) -- extensions for JDK8 `CompletableFuture` (Android API level 24).
* [kotlinx-coroutines-nio](kotlinx-coroutines-nio/README.md) -- extensions for asynchronous IO on JDK7+ (Android O Preview).

## Contributing

Follow the following simple guidelines when contributing integration with your favorite library:

* Keep it simple and general. Ideally it should fit into a single file. If it does not fit, then consider
  a separate GitHub project to host this integration.
* Follow the example of other modules. Don't fear to cut-and-paste [kotlinx-coroutines-jdk8](kotlinx-coroutines-jdk8)
  module for a start.
* Write tests and documentation, include top-level README.md with short overview and example.
* Include it into the list of modules in this file and to the top-level [pom.xml](../pom.xml).
