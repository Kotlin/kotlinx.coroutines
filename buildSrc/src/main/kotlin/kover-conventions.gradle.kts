import kotlinx.kover.api.*
import kotlinx.kover.tasks.*

/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
apply(plugin = "kover")

val notCovered = sourceless + internal + unpublished

val expectedCoverage = mutableMapOf(
    // These have lower coverage in general, it can be eventually fixed
    "kotlinx-coroutines-swing" to 70, // awaitFrame is not tested
    "kotlinx-coroutines-javafx" to 39, // JavaFx is not tested on TC because its graphic subsystem cannot be initialized in headless mode

    // Re-evaluate this along with Kover update where deprecated with error+ functions are not considered as uncovered: IDEA-287459
    "kotlinx-coroutines-reactor" to 65,
    "kotlinx-coroutines-rx2" to 78
)

extensions.configure<KoverExtension> {
    disabledProjects = notCovered
    /*
     * Is explicitly enabled on TC in a separate build step.
     * Examples:
     * ./gradlew :p:check -- doesn't verify coverage
     * ./gradlew :p:check -Pkover.enabled=true -- verifies coverage
     * ./gradlew :p:koverReport -Pkover.enabled=true -- generates report
     */
    isDisabled = !(properties["kover.enabled"]?.toString()?.toBoolean() ?: false)
}

subprojects {
    val projectName = name
    if (projectName in notCovered) return@subprojects
    tasks.withType<KoverVerificationTask> {
        rule {
            bound {
                /*
                 * 85 is our baseline that we aim to raise to 90+.
                 * Missing coverage is typically due to bugs in the agent
                 * (e.g. signatures deprecated with an error are counted),
                 * sometimes it's various diagnostic `toString` or `catch` for OOMs/VerificationErrors,
                 * but some places are definitely worth visiting.
                 */
                minValue = expectedCoverage[projectName] ?: 85 // COVERED_LINES_PERCENTAGE
            }
        }
    }

    tasks.withType<KoverHtmlReportTask> {
        htmlReportDir.set(file(rootProject.buildDir.toString() + "/kover/" + project.name + "/html"))
    }
}
