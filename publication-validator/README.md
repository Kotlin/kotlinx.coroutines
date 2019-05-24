# Publication validator

This is a supplementary subproject of kotlinx.coroutines to test its publication correctness.

It is used as part of "Dependency validation" build chain on TeamCity:
* kotlinx.corotoutines are built with `publishToMavenLocal`
* kotlinx.coroutines are built with `npmPublish -PdryRun=true` to have a packed publication
* `NpmPublicationValidator` tests that version of NPM artifact is correct and that it has neither source nor package dependencies on atomicfu
* `MavenPublicationValidator` depends on the published artifacts and tests artifacts binary content and absence of atomicfu in the classpath
