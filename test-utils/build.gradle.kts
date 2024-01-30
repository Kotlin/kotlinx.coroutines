/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

kotlin {
    sourceSets {
        commonMain.dependencies {
            api("org.jetbrains.kotlin:kotlin-test-common:${version("kotlin")}")
            api("org.jetbrains.kotlin:kotlin-test-annotations-common:${version("kotlin")}")
        }
        jvmMain.dependencies {
            api("org.jetbrains.kotlin:kotlin-test:${version("kotlin")}")
            // Workaround to make addSuppressed work in tests
            api("org.jetbrains.kotlin:kotlin-reflect:${version("kotlin")}")
            api("org.jetbrains.kotlin:kotlin-stdlib-jdk7:${version("kotlin")}")
            api("org.jetbrains.kotlin:kotlin-test-junit:${version("kotlin")}")
            api("junit:junit:${version("junit")}")
        }
        jsMain.dependencies {
            api("org.jetbrains.kotlin:kotlin-test-js:${version("kotlin")}")
        }
        val wasmJsMain by getting {
            dependencies {
                api("org.jetbrains.kotlin:kotlin-test-wasm-js:${version("kotlin")}")
            }
        }
    }
}
