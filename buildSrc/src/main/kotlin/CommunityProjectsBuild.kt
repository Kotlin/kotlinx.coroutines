/*
 * Copyright 2016-2022 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:JvmName("CommunityProjectsBuild")

import org.gradle.api.*
import org.gradle.api.artifacts.dsl.*
import java.net.*
import java.util.logging.*

private val LOGGER: Logger = Logger.getLogger("Kotlin settings logger")


/**
 * Functions in this file are responsible for configuring kotlinx.coroutines build against a custom dev version
 * of Kotlin compiler.
 * Such configuration is used in a composite community build of Kotlin in order to check whether not-yet-released changes
 * are compatible with our libraries (aka "integration testing that substitues lack of unit testing").
 */

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
