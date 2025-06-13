# Contributing Guidelines

There are two main ways to contribute to the project &mdash; submitting issues and submitting 
fixes/changes/improvements via pull requests.

## Submitting issues

Both bug reports and feature requests are welcome.
Submit issues [here](https://github.com/Kotlin/kotlinx.coroutines/issues).
Questions about usage and general inquiries are better suited for [StackOverflow](https://stackoverflow.com)
or the `#coroutines` channel in [KotlinLang Slack](https://surveys.jetbrains.com/s3/kotlin-slack-sign-up).
There, questions get answered much quicker than they do in this issue tracker,
while also reducing the load on the maintainers.

### Commenting on issues

Describing why you're interested in some specific issue helps us a lot with looking for the best solution.
The more experiences, concerns, or suggestions get shared, the better!
If you feel that something you know hasn't been said (or even if the issue discussion is too long to actually
make sure of it), please do not hesitate to drop a line.

On the other hand, "+1"-style remarks or questions about the progress on an issue do not bring anything new
and only create noise, complicating the job of finding insight in the discussion.
Please avoid this. We reserve the right to delete such comments.

## Submitting PRs

We love PRs. Submit PRs [here](https://github.com/Kotlin/kotlinx.coroutines/pulls).
However, please keep in mind that maintainers will have to support the resulting code of the project,
so do familiarize yourself with the following guidelines. 

* Before introducing a code change,
* All development (both new features and bug fixes) is performed in the `develop` branch.
  * The `master` branch contains the sources of the most recently released version.
  * Base your PRs against the `develop` branch.
  * The `develop` branch is pushed to the `master` branch during release.
  * Documentation in markdown files can be updated directly in the `master` branch, 
    unless the documentation is in the source code, and the patch changes line numbers.
* If you fix documentation:
  * After fixing/changing code examples in the [`docs`](docs) folder or updating any references in the markdown files
    run the [Knit tool](#running-the-knit-tool) and commit the resulting changes as well. 
    The tests will not pass otherwise.
  * If you plan extensive rewrites/additions to the docs, then please [contact the maintainers](#contacting-maintainers)
    to coordinate the work in advance.
* If you make any code changes:
  * Follow the [Kotlin Coding Conventions](https://kotlinlang.org/docs/reference/coding-conventions.html). 
    Use 4 spaces for indentation.
    Do not add extra newlines in function bodies: if you feel that blocks of code should be logically separated,
    then separate them with a comment instead.
  * [Build the project](#building) to make sure everything works and passes the tests.
* If you fix a bug:
  * Note that what is a bug for some can be a feature for others.
    Are you truly fixing a problem? Is there an open issue about it?
  * Write the test that reproduces the bug.
  * Fixes without tests are accepted only in exceptional circumstances if it can be shown that writing the 
    corresponding test is too hard or otherwise impractical.
  * Follow the style of writing tests that is used in this project: 
    name test functions as `testXxx`. Don't use backticks in test names.
* If you introduce any new public APIs:
  * Before setting out to work on a problem, comment on the existing issue or create one,
    proposing a solution and gathering feedback first before implementing it.
    PRs that add new API without the corresponding issue with positive feedback about the proposed implementation are
    very unlikely to be approved or reviewed.
  * All new APIs must come with documentation and tests.
  * All new APIs are initially released with the `@ExperimentalCoroutineApi` annotation and graduate later.
  * [Update the public API dumps](#updating-the-public-api-dump) and commit the resulting changes as well. 
    It will not pass the tests otherwise.

## Building

This library is built with Gradle. 

* Run `./gradlew build` to build, also running all of the tests.
* Run `./gradlew <module>:check` to test the module you are working with to speed
  things up during development.
* Run `./gradlew <module>:jvmTest` to perform only the fast JVM tests of a multiplatform module.
* Run `./gradlew <module>:jvmTest -Pstress=true` to run both fast and slow JVM tests.

### Environment requirements

JDK >= 11 referred to by the `JAVA_HOME` environment variable.

### Running the Knit tool

* Use [Knit](https://github.com/Kotlin/kotlinx-knit/blob/main/README.md) for updates to documentation:
  * Run `./gradlew knit` to update the example files, links, tables of content.
  * Commit the updated documents and examples together with other changes.

### Updating the public API dump

* Use the [Binary Compatibility Validator](https://github.com/Kotlin/binary-compatibility-validator/blob/master/README.md) for updates to public API:
  * Run `./gradlew apiDump` to update API index files. 
  * Commit the updated API indexes together with other changes.

## Releases

* The full release procedure checklist is [here](RELEASE.md).

## Contacting maintainers

* If something cannot be done, not convenient, or does not work &mdash; submit an [issue](#submitting-issues).
* "How to do something" questions &mdash; [StackOverflow](https://stackoverflow.com).
* Discussions and general inquiries &mdash; use `#coroutines` channel in [KotlinLang Slack](https://kotl.in/slack).
