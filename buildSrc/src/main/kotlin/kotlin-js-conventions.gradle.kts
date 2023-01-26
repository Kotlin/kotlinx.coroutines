/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

// Platform-specific configuration to compile JS modules

import org.jetbrains.kotlin.gradle.dsl.KotlinJsCompile
import org.jetbrains.kotlin.gradle.targets.js.*

plugins {
    kotlin("js")
}

dependencies {
    testImplementation(kotlin("test-js"))
}

kotlin {
    js(IR) {
        moduleName = project.name.removeSuffix("-js")
    }

    sourceSets {
        main {
            kotlin.srcDirs("src")
            resources.srcDirs("resources")
        }
        test {
            kotlin.srcDirs("test")
            resources.srcDirs("test-resources")
        }
    }
}

tasks.withType<KotlinJsCompile> {
    kotlinOptions {
        moduleKind = "umd"
        sourceMap = true
        metaInfo = true
    }
}
