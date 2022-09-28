/*
 * Copyright 2016-2022 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

import org.jetbrains.kotlin.gradle.tasks.*

configure(subprojects) {
    if (name in sourceless) return@configure
    apply(plugin = "kotlinx-atomicfu")
    val projectName = name
    tasks.withType(KotlinCompile::class).all {
        val isMainTaskName = name == "compileKotlin" || name == "compileKotlinJvm"
        kotlinOptions {
            if (isMainTaskName) {
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
