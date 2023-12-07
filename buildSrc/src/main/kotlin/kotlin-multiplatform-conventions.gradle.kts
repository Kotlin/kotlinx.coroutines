/*
 * Copyright 2016-2023 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

import org.gradle.api.*
import org.gradle.api.tasks.testing.logging.*
import org.jetbrains.kotlin.gradle.dsl.*
import org.jetbrains.kotlin.gradle.plugin.*

// JVM

plugins {
    kotlin("multiplatform")
}

java {
    sourceCompatibility = JavaVersion.VERSION_1_8
    targetCompatibility = JavaVersion.VERSION_1_8
}

kotlin {
    jvm {}
    jvm().compilations.all {
        compilerOptions.configure {
            jvmTarget.set(JvmTarget.JVM_1_8)
        }
    }

    jvmToolchain(jdkToolchainVersion)

    sourceSets {
        jvmMain.dependencies {
            compileOnly("org.codehaus.mojo:animal-sniffer-annotations:1.20")
            // Workaround until https://github.com/JetBrains/kotlin/pull/4999 is picked up
            api("org.jetbrains:annotations:23.0.0")
        }

        jvmTest.dependencies {
            api("org.jetbrains.kotlin:kotlin-test:${version("kotlin")}")
            // Workaround to make addSuppressed work in tests
            api("org.jetbrains.kotlin:kotlin-reflect:${version("kotlin")}")
            api("org.jetbrains.kotlin:kotlin-stdlib-jdk7:${version("kotlin")}")
            api("org.jetbrains.kotlin:kotlin-test-junit:${version("kotlin")}")
            api("junit:junit:${version("junit")}")
        }
    }
}

tasks.named("jvmTest", Test::class) {
    testLogging {
        showStandardStreams = true
        events = setOf(TestLogEvent.PASSED, TestLogEvent.FAILED)
    }

    val stressTest = project.properties["stressTest"]
    if (stressTest != null) {
        systemProperty("stressTest", "stressTest")
    }
}

// COMMON

val kotlin_version: String? by ext

kotlin.sourceSets {
    commonTest {
        dependencies {
            api("org.jetbrains.kotlin:kotlin-test-common:$kotlin_version")
            api("org.jetbrains.kotlin:kotlin-test-annotations-common:$kotlin_version")
        }
    }
}

kotlin.sourceSets.matching { it.name.contains("Main") }.forEach { srcSet ->
    project.ext.set("kotlin.mpp.freeCompilerArgsForSourceSet.${srcSet.name}", "-Xexplicit-api=strict")
}

// NATIVE

if (nativeTargetsAreEnabled) {
    val nativeMainSets = mutableListOf<KotlinSourceSet>()
    val nativeTestSets = mutableListOf<KotlinSourceSet>()
    kotlin {
        fun TargetsFromPresetExtension.addTarget(name: String) {
            val preset = presets.getByName(name)
            val target = fromPreset(preset, preset.name)
            nativeMainSets.add(target.compilations["main"].kotlinSourceSets.first())
            nativeTestSets.add(target.compilations["test"].kotlinSourceSets.first())
        }

        targets {
            // According to https://kotlinlang.org/docs/native-target-support.html
            // Tier 1
            addTarget("linuxX64")
            addTarget("macosX64")
            addTarget("macosArm64")
            addTarget("iosSimulatorArm64")
            addTarget("iosX64")

            // Tier 2
            addTarget("linuxArm64")
            addTarget("watchosSimulatorArm64")
            addTarget("watchosX64")
            addTarget("watchosArm32")
            addTarget("watchosArm64")
            addTarget("tvosSimulatorArm64")
            addTarget("tvosX64")
            addTarget("tvosArm64")
            addTarget("iosArm64")

            // Tier 3
            addTarget("androidNativeArm32")
            addTarget("androidNativeArm64")
            addTarget("androidNativeX86")
            addTarget("androidNativeX64")
            addTarget("mingwX64")
            addTarget("watchosDeviceArm64")
        }

        sourceSets {
            nativeMain { dependsOn(commonMain.get()) }
            nativeTest { dependsOn(commonTest.get()) }

            configure(nativeMainSets) { dependsOn(nativeMain.get()) }
            configure(nativeTestSets) { dependsOn(nativeTest.get()) }
        }
    }
}

// JS

kotlin {
    js {
        moduleName = project.name
        nodejs()
        compilations["main"]?.dependencies {
            api("org.jetbrains.kotlinx:atomicfu-js:${version("atomicfu")}")
        }
    }
    @OptIn(org.jetbrains.kotlin.gradle.targets.js.dsl.ExperimentalWasmDsl::class)
    wasmJs {
        moduleName = project.name + "Wasm" // Module name should be different from the one from JS
        nodejs()
        compilations["main"]?.dependencies {
            api("org.jetbrains.kotlinx:atomicfu-wasm-js:${version("atomicfu")}")
        }
    }
}

kotlin {
    sourceSets {
        val jsAndWasmSharedMain by registering {
            dependsOn(commonMain.get())
        }
        val jsAndWasmSharedTest by registering {
            dependsOn(commonTest.get())
        }
        jsMain {
            dependsOn(jsAndWasmSharedMain.get())
        }
        jsTest {
            dependsOn(jsAndWasmSharedTest.get())
        }

        jsTest.dependencies {
            api("org.jetbrains.kotlin:kotlin-test-js:$kotlin_version")
        }
        val wasmJsMain by getting {
            dependsOn(jsAndWasmSharedMain.get())
        }
        val wasmJsTest by getting {
            dependsOn(jsAndWasmSharedTest.get())
        }
        wasmJsTest.dependencies {
            api("org.jetbrains.kotlin:kotlin-test-wasm-js:$kotlin_version")
        }
    }
}

// Disable intermediate sourceSet compilation because we do not need js-wasmJs artifact
tasks.configureEach {
    if (name == "compileJsAndWasmSharedMainKotlinMetadata") {
        enabled = false
    }
}
