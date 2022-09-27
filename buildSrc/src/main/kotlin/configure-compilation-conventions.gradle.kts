/*
 * Copyright 2016-2022 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

import org.jetbrains.kotlin.gradle.tasks.*

val graduallyIntroducedWarningAsErrorProjects = setOf(
    // UI
    "kotlinx-coroutines-android",
    "kotlinx-coroutines-javafx",
    "kotlinx-coroutines-swing",

    // Reactive
    "kotlinx-coroutines-jdk9",
    "kotlinx-coroutines-reactive",
    "kotlinx-coroutines-reactor",
    "kotlinx-coroutines-rx2",
    "kotlinx-coroutines-rx3",

    // Integration
    "kotlinx-coroutines-guava",
    "kotlinx-coroutines-jdk8",
    "kotlinx-coroutines-play-services",
    "kotlinx-coroutines-slf4j",

    // Top-level
    "kotlinx-coroutines-debug",

    )

configure(subprojects) {
    if (name in sourceless) return@configure
    apply(plugin = "kotlinx-atomicfu")
    val projectName = name
    tasks.withType(KotlinCompile::class).all {
        val isMainTaskName = name == "compileKotlin" || name == "compileKotlinJvm"
        kotlinOptions {
            if (projectName in graduallyIntroducedWarningAsErrorProjects && isMainTaskName) {
                allWarningsAsErrors = true
            }
            val newOptions =
                listOf(
                    "-progressive", "-Xno-param-assertions", "-Xno-receiver-assertions",
                    "-Xno-call-assertions"
                ) + optInAnnotations.map { "-opt-in=$it" }
            freeCompilerArgs = freeCompilerArgs + newOptions
        }
    }
}
