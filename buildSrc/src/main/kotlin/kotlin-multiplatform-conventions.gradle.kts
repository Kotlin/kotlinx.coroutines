/*
 * Copyright 2016-2023 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

import org.gradle.api.*
import org.gradle.api.tasks.testing.logging.*
import org.jetbrains.kotlin.gradle.dsl.*

plugins {
    kotlin("multiplatform")
}

java {
    sourceCompatibility = JavaVersion.VERSION_1_8
    targetCompatibility = JavaVersion.VERSION_1_8
}

kotlin {
    jvm {
        compilations.all {
            compilerOptions.configure {
                jvmTarget = JvmTarget.JVM_1_8
            }
        }
    }
    jvmToolchain(jdkToolchainVersion)
    if (nativeTargetsAreEnabled) {
        // According to https://kotlinlang.org/docs/native-target-support.html
        // Tier 1
        linuxX64()
        macosX64()
        macosArm64()
        iosSimulatorArm64()
        iosX64()
        // Tier 2
        linuxArm64()
        watchosSimulatorArm64()
        watchosX64()
        watchosArm32()
        watchosArm64()
        tvosSimulatorArm64()
        tvosX64()
        tvosArm64()
        iosArm64()
        // Tier 3
        androidNativeArm32()
        androidNativeArm64()
        androidNativeX86()
        androidNativeX64()
        mingwX64()
        watchosDeviceArm64()
    }
    js {
        moduleName = project.name
        nodejs()
        compilations["main"]?.dependencies {
            api("org.jetbrains.kotlinx:atomicfu-js:${version("atomicfu")}")
        }
    }
    @OptIn(org.jetbrains.kotlin.gradle.targets.js.dsl.ExperimentalWasmDsl::class)
    wasmJs {
        // Module name should be different from the one from JS
        // otherwise IC tasks that start clashing different modules with the same module name
        moduleName = project.name + "Wasm"
        nodejs()
        compilations["main"]?.dependencies {
            api("org.jetbrains.kotlinx:atomicfu-wasm-js:${version("atomicfu")}")
        }
    }
    applyDefaultHierarchyTemplate()
    sourceSets {
        commonTest {
            dependencies {
                api("org.jetbrains.kotlin:kotlin-test-common:${version("kotlin")}")
                api("org.jetbrains.kotlin:kotlin-test-annotations-common:${version("kotlin")}")
            }
        }
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
        nativeMain.dependencies {
            // workaround for #3968 until this is fixed on atomicfu's side
            api("org.jetbrains.kotlinx:atomicfu:0.23.1")
        }
        jsMain { }
        jsTest {
            dependencies {
                api("org.jetbrains.kotlin:kotlin-test-js:${version("kotlin")}")
            }
        }
        val wasmJsMain by getting {
        }
        val wasmJsTest by getting {
            dependencies {
                api("org.jetbrains.kotlin:kotlin-test-wasm-js:${version("kotlin")}")
            }
        }
        groupSourceSets("jsAndWasmShared", listOf("js", "wasmJs"), listOf("common"))
    }
}

// Disable intermediate sourceSet compilation because we do not need js-wasmJs artifact
tasks.configureEach {
    if (name == "compileJsAndWasmSharedMainKotlinMetadata") {
        enabled = false
    }
}

tasks.named("jvmTest", Test::class) {
    testLogging {
        showStandardStreams = true
        events = setOf(TestLogEvent.PASSED, TestLogEvent.FAILED)
    }
    project.properties["stressTest"]?.let { systemProperty("stressTest", it) }
}
