/*
 * Copyright 2016-2022 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

import org.jetbrains.kotlin.gradle.dsl.KotlinCompile
import org.jetbrains.kotlin.gradle.dsl.KotlinCommonOptions

configure(subprojects) {
    val project = this
    if (name in sourceless) return@configure
    apply(plugin = "kotlinx-atomicfu")
    tasks.withType<KotlinCompile<*>>().configureEach {
        val isMainTaskName = name == "compileKotlin" || name == "compileKotlinJvm"
        kotlinOptions {
            languageVersion = getOverriddenKotlinLanguageVersion(project)
            apiVersion = getOverriddenKotlinApiVersion(project)
            if (isMainTaskName && versionsAreNotOverridden) {
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

val KotlinCommonOptions.versionsAreNotOverridden: Boolean
    get() = languageVersion == null && apiVersion == null