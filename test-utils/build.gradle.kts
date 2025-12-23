/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

kotlin {
    sourceSets {
        val concurrentMain by creating {
            configureDirectoryPaths()
            dependsOn(commonMain.get())
        }
        commonMain.dependencies {
            api("org.jetbrains.kotlin:kotlin-test:${version("kotlin")}")
        }
        jvmMain.dependencies {
            // Workaround to make addSuppressed work in tests
            api("org.jetbrains.kotlin:kotlin-reflect:${version("kotlin")}")
            api("org.jetbrains.kotlin:kotlin-stdlib-jdk7:${version("kotlin")}")
            api("org.jetbrains.kotlin:kotlin-test-junit:${version("kotlin")}")
            api("junit:junit:${version("junit")}")
        }
        jvmMain { dependsOn(concurrentMain) }
        nativeMain { dependsOn(concurrentMain) }
    }
}
