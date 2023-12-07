/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
import org.jetbrains.kotlin.gradle.plugin.*

fun KotlinSourceSet.configureDirectoryPaths() {
    if (project.isMultiplatform) {
        val srcDir = if (name.endsWith("Main")) "src" else "test"
        val platform = name.dropLast(4)
        kotlin.srcDir("$platform/$srcDir")
        if (name == "jvmMain") {
            resources.srcDir("$platform/resources")
        } else if (name == "jvmTest") {
            resources.srcDir("$platform/test-resources")
        }
    } else if (platformOf(project) == "jvm") {
        when (name) {
            "main" -> {
                kotlin.srcDir("src")
                resources.srcDir("resources")
            }
            "test" -> {
                kotlin.srcDir("test")
                resources.srcDir("test-resources")
            }
        }
    } else {
        throw IllegalArgumentException("Unclear how to configure source sets for ${project.name}")
    }
}
