/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:JvmName("Projects")
import org.gradle.api.Project

fun Project.version(target: String): String =
    property("${target}_version") as String

val coreModule = "kotlinx-coroutines-core"
val testModule = "kotlinx-coroutines-test"

val multiplatform = setOf(coreModule, testModule)
// Not applicable for Kotlin plugin
val sourceless = setOf("kotlinx.coroutines", "kotlinx-coroutines-bom", "integration-testing")
val internal = setOf("kotlinx.coroutines", "benchmarks", "integration-testing")
// Not published
val unpublished = internal + setOf("example-frontend-js", "android-unit-tests")

val Project.isMultiplatform: Boolean get() = name in multiplatform
