/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

// Platform-specific configuration to compile JVM modules

import org.gradle.api.*

plugins {
    kotlin("jvm")
}

java {
    sourceCompatibility = JavaVersion.VERSION_1_6
    targetCompatibility = JavaVersion.VERSION_1_6
}

if (rootProject.extra.get("jvm_ir_enabled") as Boolean) {
    kotlin.target.compilations.configureEach {
        kotlinOptions.useIR = true
    }
}

dependencies {
    testCompile(kotlin("test"))
    // Workaround to make addSuppressed work in tests
    testCompile(kotlin("reflect"))
    testCompile(kotlin("stdlib-jdk7"))
    testCompile(kotlin("test-junit"))
    testCompile("junit:junit:${version("junit")}")
}

tasks.compileKotlin {
    kotlinOptions {
        freeCompilerArgs += listOf("-Xexplicit-api=strict")
    }
}

tasks.withType<Test> {
    testLogging {
        showStandardStreams = true
        events("passed", "failed")
    }
    val stressTest = project.properties["stressTest"]
    if (stressTest != null) systemProperties["stressTest"] = stressTest
}
