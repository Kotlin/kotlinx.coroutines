/*
 * Copyright 2016-2022 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:JvmName("CommunityProjectsBuild")

import org.gradle.api.*
import org.gradle.api.artifacts.dsl.*
import org.gradle.api.tasks.testing.Test
import org.gradle.kotlin.dsl.*
import java.net.*
import java.util.logging.*

private val LOGGER: Logger = Logger.getLogger("Kotlin settings logger")


/**
 * Functions in this file are responsible for configuring kotlinx.coroutines build against a custom dev version
 * of Kotlin compiler.
 * Such configuration is used in a composite community build of Kotlin in order to check whether not-yet-released changes
 * are compatible with our libraries (aka "integration testing that substitutes lack of unit testing").
 */

/**
 * Should be used for running against of non-released Kotlin compiler on a system test level.
 *
 * @return a Kotlin API version parametrized from command line nor gradle.properties, null otherwise
 */
fun getOverriddenKotlinApiVersion(project: Project): String? {
    val apiVersion = project.rootProject.properties["kotlin_api_version"] as? String
    if (apiVersion != null) {
        LOGGER.info("""Configured Kotlin API version: '$apiVersion' for project $${project.name}""")
    }
    return apiVersion
}

/**
 * Should be used for running against of non-released Kotlin compiler on a system test level
 *
 * @return a Kotlin Language version parametrized from command line nor gradle.properties, null otherwise
 */
fun getOverriddenKotlinLanguageVersion(project: Project): String? {
    val languageVersion = project.rootProject.properties["kotlin_language_version"] as? String
    if (languageVersion != null) {
        LOGGER.info("""Configured Kotlin Language version: '$languageVersion' for project ${project.name}""")
    }
    return languageVersion
}

/**
 * Should be used for running against of non-released Kotlin compiler on a system test level
 * Kotlin compiler artifacts are expected to be downloaded from maven central by default.
 * In case of compiling with not-published into the MC kotlin compiler artifacts, a kotlin_repo_url gradle parameter should be specified.
 * To reproduce a build locally, a kotlin/dev repo should be passed
 *
 * @return an url for a kotlin compiler repository parametrized from command line nor gradle.properties, empty string otherwise
 */
fun getKotlinDevRepositoryUrl(project: Project): URI? {
    val url: String? = project.rootProject.properties["kotlin_repo_url"] as? String
    if (url != null) {
        LOGGER.info("""Configured Kotlin Compiler repository url: '$url' for project ${project.name}""")
        return URI.create(url)
    }
    return null
}

/**
 * Adds a kotlin-dev space repository with dev versions of Kotlin if Kotlin aggregate build is enabled
 */
fun addDevRepositoryIfEnabled(rh: RepositoryHandler, project: Project) {
    val devRepoUrl = getKotlinDevRepositoryUrl(project) ?: return
    rh.maven {
        url = devRepoUrl
    }
}

/**
 * Changes the build config when 'build_snapshot_train' is enabled:
 * Disables flaky and Kotlin-specific tests, prints the real version of Kotlin applied (to be sure overridden version of Kotlin is properly picked).
 */
fun Project.configureCommunityBuildTweaks() {
    // Flag that detects whether community build is enabled
    val buildSnapshotTrain = (project.rootProject.properties["build_snapshot_train"] as? String) != null
    if (!buildSnapshotTrain) return

    allprojects {
        // Disable stress tests and tests that are flaky on Kotlin version specific
        tasks.withType<Test>().configureEach {
            exclude("**/*LinearizabilityTest*")
            exclude("**/*LFTest*")
            exclude("**/*StressTest*")
            exclude("**/*scheduling*")
            exclude("**/*Timeout*")
            exclude("**/*definitely/not/kotlinx*")
            exclude("**/*PrecompiledDebugProbesTest*")
        }
    }

    println("Manifest of kotlin-compiler-embeddable.jar for coroutines")
    val coreProject = subprojects.single { it.name == coreModule }
    configure(listOf(coreProject)) {
        configurations.matching { it.name == "kotlinCompilerClasspath" }.configureEach {
            val config = resolvedConfiguration.files.single { it.name.contains("kotlin-compiler-embeddable") }

            val manifest = zipTree(config).matching {
                include("META-INF/MANIFEST.MF")
            }.files.single()

            manifest.readLines().forEach {
                println(it)
            }
        }
    }
}
