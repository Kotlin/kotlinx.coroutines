/*
 * Copyright 2016-2023 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

// Platform-specific configuration to compile JVM modules

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
