# Coroutines integration

This directory contains modules that provide integration with various asynchronous callback- and future-based libraries:

## Modules

* [kotlinx-coroutines-jdk8](kotlinx-coroutines-jdk8/README.md) -- integration with JDK8 `CompletableFuture` (Android API level 24).
* [kotlinx-coroutines-nio](kotlinx-coroutines-nio/README.md) -- integration with asynchronous IO on JDK7+ (Android O Preview).
* [kotlinx-coroutines-guava](kotlinx-coroutines-guava/README.md) -- integration with Guava [ListenableFuture](https://github.com/google/guava/wiki/ListenableFutureExplained).

## Contributing

Follow the following simple guidelines when contributing integration with your favorite library:

* Keep it simple and general. Ideally it should fit into a single file. If it does not fit, then consider
  a separate GitHub project to host this integration.
* Follow the example of other modules. 
  Cut-and-paste [kotlinx-coroutines-guava](kotlinx-coroutines-guava) module as a template.
* Write tests and documentation, include top-level `README.md` with short overview and example.
* Reference the new module from all the places:
  * List of modules in this document.
  * List of modules in top-level [`pom.xml`](../pom.xml).
  * List of dependencies for documentation site in [`site/pom.xml`](../site/pom.xml).
  * List of directories for documentation site in [`site/build.xml`](../site/build.xml).
  * List of modules at the root of documentation site in [`site/docs/index.md`](../site/docs/index.md).
* Update links to documentation website as explained [here](../knit/README.md#usage).
* Squash your contribution to a single commit and create pull request to `develop` branch.
