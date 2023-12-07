/*
 * Copyright 2016-2023 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

import org.gradle.api.*
import org.gradle.api.tasks.testing.logging.*
import org.jetbrains.kotlin.gradle.dsl.*
import org.jetbrains.kotlin.gradle.plugin.*
import org.jetbrains.kotlin.gradle.plugin.mpp.*

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

// NATIVE

if (nativeTargetsAreEnabled) {
    kotlin {
        val targets = buildList<KotlinNativeTarget> {
            // According to https://kotlinlang.org/docs/native-target-support.html
            // Tier 1
            add(linuxX64())
            add(macosX64())
            add(macosArm64())
            add(iosSimulatorArm64())
            add(iosX64())
            // Tier 2
            add(linuxArm64())
            add(watchosSimulatorArm64())
            add(watchosX64())
            add(watchosArm32())
            add(watchosArm64())
            add(tvosSimulatorArm64())
            add(tvosX64())
            add(tvosArm64())
            add(iosArm64())
            // Tier 3
            add(androidNativeArm32())
            add(androidNativeArm64())
            add(androidNativeX86())
            add(androidNativeX64())
            add(mingwX64())
            add(watchosDeviceArm64())
        }

        sourceSets {
            commonMain
            commonTest
            nativeMain {
                dependsOn(commonMain.get())
            }
            nativeTest {
                dependsOn(commonTest.get())
            }
            for (target in targets) {
                named(target.name + "Main") { dependsOn(nativeMain.get()) }
                named(target.name + "Test") { dependsOn(nativeTest.get()) }
            }
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
            dependencies {
                api("org.jetbrains.kotlin:kotlin-test-js:$kotlin_version")
            }
        }
        val wasmJsMain by getting {
            dependsOn(jsAndWasmSharedMain.get())
        }
        val wasmJsTest by getting {
            dependsOn(jsAndWasmSharedTest.get())
            dependencies {
                api("org.jetbrains.kotlin:kotlin-test-wasm-js:$kotlin_version")
            }
        }
    }
}

// Disable intermediate sourceSet compilation because we do not need js-wasmJs artifact
tasks.configureEach {
    if (name == "compileJsAndWasmSharedMainKotlinMetadata") {
        enabled = false
    }
}
