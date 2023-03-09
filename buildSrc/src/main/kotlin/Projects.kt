/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:JvmName("Projects")
import org.gradle.api.*

fun Project.version(target: String): String =
    property("${target}_version") as String

val coreModule = "kotlinx-coroutines-core"
val jdk8ObsoleteModule = "kotlinx-coroutines-jdk8"
val testModule = "kotlinx-coroutines-test"

val multiplatform = setOf(coreModule, testModule)
// Not applicable for Kotlin plugin
val sourceless = setOf("kotlinx.coroutines", "kotlinx-coroutines-bom")
val internal = setOf("kotlinx.coroutines", "benchmarks")
// Not published
val unpublished = internal + setOf("example-frontend-js", "android-unit-tests")

val Project.isMultiplatform: Boolean get() = name in multiplatform

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
