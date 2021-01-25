/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

project.kotlin {
    js(LEGACY) {
        binaries.executable()
        browser {
            distribution {
                directory = new File(directory.parentFile, "dist")
            }
            webpackTask {
                cssSupport.enabled = true
            }
            runTask {
                cssSupport.enabled = true
            }
            testTask {
                useKarma {
                    useChromeHeadless()
                    webpackConfig.cssSupport.enabled = true
                }
            }
        }
    }

    sourceSets {
        main.dependencies {
            implementation "org.jetbrains.kotlinx:kotlinx-html-js:$html_version"
            implementation(npm("html-webpack-plugin", "3.2.0"))
        }
    }
}
