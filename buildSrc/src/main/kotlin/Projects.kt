/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:JvmName("Projects")

import org.gradle.api.*
import org.gradle.api.tasks.*

fun Project.version(target: String): String {
    if (target == "kotlin") {
        getOverriddenKotlinVersion(this)?.let { return it }
    }
    return property("${target}_version") as String
}

val Project.jdkToolchainVersion: Int get() = property("jdk_toolchain_version").toString().toInt()

val Project.nativeTargetsAreEnabled: Boolean get() = rootProject.properties["disable_native_targets"] == null

val Project.sourceSets: SourceSetContainer get() =
    extensions.getByName("sourceSets") as SourceSetContainer


val coreModule = "kotlinx-coroutines-core"
val jdk8ObsoleteModule = "kotlinx-coroutines-jdk8"
val testModule = "kotlinx-coroutines-test"

val multiplatform = setOf(coreModule, testModule)

// Not applicable for Kotlin plugin
val sourceless = setOf("kotlinx.coroutines", "kotlinx-coroutines-bom")
val internal = setOf("kotlinx.coroutines", "benchmarks")

// Not published
val unpublished = internal + setOf("android-unit-tests")

val Project.isMultiplatform: Boolean get() = name in multiplatform
val Project.isBom: Boolean get() = name == "kotlinx-coroutines-bom"

// Projects that we do not check for Android API level 14 check due to various limitations
val androidNonCompatibleProjects = setOf(
    "kotlinx-coroutines-debug",
    "kotlinx-coroutines-swing",
    "kotlinx-coroutines-javafx",
    "kotlinx-coroutines-jdk8",
    "kotlinx-coroutines-jdk9",
    "kotlinx-coroutines-reactor",
    "kotlinx-coroutines-test"
)
