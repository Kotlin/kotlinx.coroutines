# Integration tests

This is a supplementary project that provides integration tests.

The tests are the following:
* `MavenPublicationValidator` depends on the published artifacts and tests artifacts binary content and absence of atomicfu in the classpath.
* `CoreAgentTest` checks that `kotlinx-coroutines-core` can be run as a Java agent.
* `DebugAgentTest` checks that the coroutine debugger can be run as a Java agent.
* `smokeTest` builds the test project that depends on coroutines.

The `integration-testing` project is expected to be in a subdirectory of the main `kotlinx.coroutines` project.

To run all the available tests: `cd integration-testing` + `./gradlew check`.
