/*
 * Copyright 2016-2022 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

import org.jetbrains.kotlin.gradle.dsl.KotlinCompile
import org.jetbrains.kotlin.gradle.dsl.KotlinCommonOptions
import org.jetbrains.kotlin.gradle.tasks.*

configure(subprojects) {
    val project = this
    if (name in sourceless) return@configure
    apply(plugin = "kotlinx-atomicfu")
    tasks.withType<KotlinCompile<*>>().configureEach {
        val isMainTaskName = name.startsWith("compileKotlin")
        kotlinOptions {
            languageVersion = getOverriddenKotlinLanguageVersion(project)
            apiVersion = getOverriddenKotlinApiVersion(project)
            if (isMainTaskName && versionsAreNotOverridden) {
                allWarningsAsErrors = true
                freeCompilerArgs = freeCompilerArgs + "-Xexplicit-api=strict"
            }

            /*
             * Coroutines do not interop with Java and these flags provide a significant
             * (i.e. close to double-digit) reduction in both bytecode and optimized dex size
             */
            val bytecodeSizeReductionOptions =
                if (this@configureEach is KotlinJvmCompile) listOf(
                    "-Xno-param-assertions",
                    "-Xno-call-assertions",
                    "-Xno-receiver-assertions"
                ) else emptyList()

            val newOptions = listOf(
                "-progressive", "-Xexpect-actual-classes"
            ) + bytecodeSizeReductionOptions + optInAnnotations.map { "-opt-in=$it" }
            freeCompilerArgs = freeCompilerArgs + newOptions
        }

    }
}

val KotlinCommonOptions.versionsAreNotOverridden: Boolean
    get() = languageVersion == null && apiVersion == null
