/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

import java.util.*

buildscript {
    val cacheRedirectorEnabled = System.getenv("CACHE_REDIRECTOR")?.toBoolean() == true

    if (cacheRedirectorEnabled) {
        println("Redirecting repositories for buildSrc buildscript")
    }

    repositories {
        if (cacheRedirectorEnabled) {
            maven("https://cache-redirector.jetbrains.com/plugins.gradle.org/m2")
        } else {
            maven("https://plugins.gradle.org/m2")
        }
    }
}

plugins {
    `kotlin-dsl`
}

val cacheRedirectorEnabled = System.getenv("CACHE_REDIRECTOR")?.toBoolean() == true

repositories {
    if (cacheRedirectorEnabled) {
        maven("https://cache-redirector.jetbrains.com/plugins.gradle.org/m2")
        maven("https://cache-redirector.jetbrains.com/dl.bintray.com/kotlin/kotlin-eap")
        maven("https://cache-redirector.jetbrains.com/dl.bintray.com/kotlin/kotlin-dev")
    } else {
        maven("https://plugins.gradle.org/m2")
        maven("https://dl.bintray.com/kotlin/kotlin-eap")
        maven("https://dl.bintray.com/kotlin/kotlin-dev")
    }
}

kotlinDslPluginOptions {
    experimentalWarning.set(false)
}

private val props = Properties().apply {
    file("../gradle.properties").inputStream().use { load(it) }
}

fun version(target: String): String =
    props.getProperty("${target}_version")

dependencies {
    implementation(kotlin("gradle-plugin", version("kotlin")))
    implementation("org.jetbrains.dokka:dokka-gradle-plugin:${version("dokka")}")
}
