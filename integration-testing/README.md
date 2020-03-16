# Integration tests

This is a supplementary subproject of kotlinx.coroutines that provides
integration tests.

The tests are the following:
* `NpmPublicationValidator` tests that version of NPM artifact is correct and that it has neither source nor package dependencies on atomicfu
  In order for the test to work, one needs to run gradle with `-PdryRun=true`.
  `-PdryRun` affects `npmPublish` so that it only provides a packed publication
  and does not in fact attempt to send the build for publication.
* `MavenPublicationValidator` depends on the published artifacts and tests artifacts binary content and absence of atomicfu in the classpath
* `DebugAgentTest` checks that the coroutine debugger can be run as a Java agent.

All the available tests can be run with `integration-testing:test`.
