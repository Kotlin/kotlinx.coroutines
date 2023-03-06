# Integration tests

This is a supplementary project that provides integration tests.

The tests are the following:
* `mavenTest` depends on the published artifacts and tests artifacts binary content for absence of atomicfu in the classpath.
* `jvmCoreTest` miscellaneous tests that check the behaviour of `kotlinx-coroutines-core` dependency in a smoke manner.
* `coreAgentTest` checks that `kotlinx-coroutines-core` can be run as a Java agent.
* `debugAgentTest` checks that the coroutine debugger can be run as a Java agent.
* `debugDynamicAgentTest` checks that `kotlinx-coroutines-debug` agent can self-attach dynamically to JVM as a standalone dependency.
* `smokeTest` builds the multiplatform test project that depends on coroutines.

The `integration-testing` project is expected to be in a subdirectory of the main `kotlinx.coroutines` project.

To run all the available tests: `./gradlew publishToMavenLocal` + `cd integration-testing` + `./gradlew check`.
