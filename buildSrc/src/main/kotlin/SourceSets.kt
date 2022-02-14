/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
import org.jetbrains.kotlin.gradle.plugin.*

fun KotlinSourceSet.configureMultiplatform() {
    val srcDir = if (name.endsWith("Main")) "src" else "test"
    val platform = name.dropLast(4)
    kotlin.srcDir("$platform/$srcDir")
    if (name == "jvmMain") {
        resources.srcDir("$platform/resources")
    } else if (name == "jvmTest") {
        resources.srcDir("$platform/test-resources")
    }
    languageSettings {
        optInAnnotations.forEach { optIn(it) }
        progressiveMode = true
    }
}
