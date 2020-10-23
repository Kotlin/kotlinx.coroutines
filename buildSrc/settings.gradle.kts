/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
pluginManagement {
    val build_snapshot_train: String? by settings
    repositories {
        val cacheRedirectorEnabled = System.getenv("CACHE_REDIRECTOR")?.toBoolean() == true
        if (cacheRedirectorEnabled) {
            println("Redirecting repositories for buildSrc buildscript")
            maven("https://cache-redirector.jetbrains.com/plugins.gradle.org/m2")
        } else {
            maven("https://plugins.gradle.org/m2")
        }
        if (build_snapshot_train?.toBoolean() == true) {
            mavenLocal()
        }
    }
}
