# Publication validator

This is a supplementary subproject of kotlinx.coroutines that provides a new
task, `testPublishing`, to test its publication correctness.

The tests are the following:
* `NpmPublicationValidator` tests that version of NPM artifact is correct and that it has neither source nor package dependencies on atomicfu
* `MavenPublicationValidator` depends on the published artifacts and tests artifacts binary content and absence of atomicfu in the classpath

To test publication, one needs to run gradle with `-PdryRun=true`, and the
task that actually does the testing is `publication-validator:test`.
`-PdryRun` affects `npmPublish` so that it only provides a packed publication
and does not in fact attempt to send the build for publication.
