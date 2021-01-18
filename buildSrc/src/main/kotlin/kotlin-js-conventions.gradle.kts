/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

// Platform-specific configuration to compile JS modules

apply plugin: 'org.jetbrains.kotlin.js'

dependencies {
    testImplementation "org.jetbrains.kotlin:kotlin-test-js:$kotlin_version"
}

kotlin {
    js(LEGACY) {
        moduleName = project.name - "-js"
    }

    sourceSets {
        main.kotlin.srcDirs = ['src']
        test.kotlin.srcDirs = ['test']
        main.resources.srcDirs = ['resources']
        test.resources.srcDirs = ['test-resources']
    }
}

tasks.withType(compileKotlinJs.getClass()) {
    kotlinOptions {
        moduleKind = "umd"
        sourceMap = true
        metaInfo = true
    }
}
