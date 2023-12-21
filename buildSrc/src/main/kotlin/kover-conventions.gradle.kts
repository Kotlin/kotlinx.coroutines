/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
import kotlinx.kover.gradle.plugin.dsl.*

plugins {
    id("org.jetbrains.kotlinx.kover")
}

val notCovered = sourceless + unpublished

val expectedCoverage = mutableMapOf(
    // These have lower coverage in general, it can be eventually fixed
    "kotlinx-coroutines-swing" to 70, // awaitFrame is not tested
    "kotlinx-coroutines-javafx" to 35, // JavaFx is not tested on TC because its graphic subsystem cannot be initialized in headless mode

    // Reactor has lower coverage in general due to various fatal error handling features
    "kotlinx-coroutines-reactor" to 75
)

val conventionProject = project

subprojects {
    val projectName = name
    if (projectName in notCovered) return@subprojects

    project.apply(plugin = "org.jetbrains.kotlinx.kover")
    conventionProject.dependencies.add("kover", this)

    extensions.configure<KoverProjectExtension>("kover") {
        /*
        * Is explicitly enabled on TC in a separate build step.
        * Examples:
        * ./gradlew :p:check -- doesn't verify coverage
        * ./gradlew :p:check -Pkover.enabled=true -- verifies coverage
        * ./gradlew :p:koverHtmlReport -Pkover.enabled=true -- generates HTML report
        */
        if (properties["kover.enabled"]?.toString()?.toBoolean() != true) {
            disable()
        }
    }

    extensions.configure<KoverReportExtension>("koverReport") {
        defaults {
            html {
                setReportDir(conventionProject.layout.buildDirectory.dir("kover/${project.name}/html"))
            }

            verify {
                rule {
                    /*
                    * 85 is our baseline that we aim to raise to 90+.
                    * Missing coverage is typically due to bugs in the agent
                    * (e.g. signatures deprecated with an error are counted),
                    * sometimes it's various diagnostic `toString` or `catch` for OOMs/VerificationErrors,
                    * but some places are definitely worth visiting.
                    */
                    minBound(expectedCoverage[projectName] ?: 85) // COVERED_LINES_PERCENTAGE
                }
            }
        }
    }
}

koverReport {
    defaults {
        verify {
            rule {
                minBound(85) // COVERED_LINES_PERCENTAGE
            }
        }
    }
}

conventionProject.tasks.register("koverReport") {
    dependsOn(conventionProject.tasks.named("koverHtmlReport"))
}
