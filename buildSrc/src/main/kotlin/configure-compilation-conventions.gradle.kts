/*
 * Copyright 2016-2022 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

import org.jetbrains.kotlin.gradle.dsl.*
import org.jetbrains.kotlin.gradle.dsl.KotlinCompile
import org.jetbrains.kotlin.gradle.tasks.*
import org.jetbrains.kotlin.gradle.tasks.KotlinJvmCompile

configure(subprojects) {
    val project = this
    if (name in sourceless) return@configure
    apply(plugin = "kotlinx-atomicfu")
    tasks.withType<KotlinCompilationTask<*>>().configureEach {
        val isMainTaskName = name.startsWith("compileKotlin")
        compilerOptions {
            var versionsAreNotOverridden = true
            getOverriddenKotlinLanguageVersion(project)?.let {
                languageVersion = it
                versionsAreNotOverridden = false
            }
            getOverriddenKotlinApiVersion(project)?.let {
                apiVersion = it
                versionsAreNotOverridden = false
            }
            if (isMainTaskName && versionsAreNotOverridden) {
                allWarningsAsErrors = true
                freeCompilerArgs.add("-Xexplicit-api=strict")
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
            freeCompilerArgs.addAll(newOptions)
        }

    }
}
