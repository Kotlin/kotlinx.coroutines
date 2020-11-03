/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("UnstableApiUsage")

import me.champeau.gradle.*
import org.jetbrains.kotlin.gradle.tasks.*

plugins {
    id("net.ltgt.apt")
    id("com.github.johnrengelman.shadow")
    id("me.champeau.gradle.jmh") apply false
}

repositories {
    maven("https://repo.typesafe.com/typesafe/releases/")
}

java {
    sourceCompatibility = JavaVersion.VERSION_1_8
    targetCompatibility = JavaVersion.VERSION_1_8
}

apply(plugin="me.champeau.gradle.jmh")

tasks.named<KotlinCompile>("compileJmhKotlin") {
    kotlinOptions {
        jvmTarget = "1.8"
        freeCompilerArgs += "-Xjvm-default=enable"
    }
}



// It is better to use the following to run benchmarks, otherwise you may get unexpected errors:
// ./gradlew --no-daemon cleanJmhJar jmh -Pjmh="MyBenchmark"
extensions.configure<JMHPluginExtension>("jmh") {
    jmhVersion = "1.26"
    duplicateClassesStrategy = DuplicatesStrategy.INCLUDE
    failOnError = true
    resultFormat = "CSV"
    project.findProperty("jmh")?.also {
        include = listOf(".*$it.*")
    }
//    includeTests = false
}

tasks.named<Jar>("jmhJar") {
    archiveBaseName by "benchmarks"
    archiveClassifier by null
    archiveVersion by null
    destinationDirectory.file("$rootDir")
}

dependencies {
    compile("org.openjdk.jmh:jmh-core:1.26")
    compile("io.projectreactor:reactor-core:${version("reactor")}")
    compile("io.reactivex.rxjava2:rxjava:2.1.9")
    compile("com.github.akarnokd:rxjava2-extensions:0.20.8")

    compile("com.typesafe.akka:akka-actor_2.12:2.5.0")
    compile(project(":kotlinx-coroutines-core"))

    // add jmh dependency on main
    "jmhImplementation"(sourceSets.main.get().runtimeClasspath)
}
