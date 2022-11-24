/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

kotlin {
    js(LEGACY) {
        binaries.executable()
        browser {
            distribution {
                directory = directory.parentFile.resolve("dist")
            }
             commonWebpackConfig {
                 cssSupport {
                     enabled.set(true)
                 }
             }
            testTask {
                useKarma {
                    useChromeHeadless()
                }
            }
        }
    }
}

// For kotlinx-html
repositories {
    maven("https://maven.pkg.jetbrains.space/public/p/kotlinx-html/maven")
}

dependencies {
    implementation("org.jetbrains.kotlinx:kotlinx-html-js:${version("html")}")
    implementation(devNpm("html-webpack-plugin", "5.3.1"))
}
