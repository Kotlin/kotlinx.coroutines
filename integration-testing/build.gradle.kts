/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

import org.jetbrains.kotlin.gradle.dsl.*

buildscript {

    /*
     * These property group is used to build kotlinx.coroutines against Kotlin compiler snapshot.
     * How does it work:
     * When build_snapshot_train is set to true, kotlin_version property is overridden with kotlin_snapshot_version,
     * atomicfu_version is overwritten by TeamCity environment (AFU is built with snapshot and published to mavenLocal
     * as previous step or the snapshot build).
     * Additionally, mavenLocal and Sonatype snapshots are added to repository list and stress tests are disabled.
     * DO NOT change the name of these properties without adapting kotlinx.train build chain.
     */
    extra["build_snapshot_train"] = rootProject.properties["build_snapshot_train"].let { it != null && it != "" }
    val build_snapshot_train: Boolean by extra
    if (build_snapshot_train) {
        extra["kotlin_version"] = rootProject.properties["kotlin_snapshot_version"]
        val kotlin_version: String? by extra
        if (kotlin_version == null) {
            throw IllegalArgumentException("'kotlin_snapshot_version' should be defined when building with snapshot compiler")
        }
    }
    extra["native_targets_enabled"] = rootProject.properties["disable_native_targets"] == null

    // Determine if any project dependency is using a snapshot version
    extra["using_snapshot_version"] = build_snapshot_train

    rootProject.properties.forEach { key, value ->
        if (key.endsWith("_version") && value is String && value.endsWith("-SNAPSHOT")) {
            println("NOTE: USING SNAPSHOT VERSION: $key=$value")
            extra["using_snapshot_version"] = true
        }
    }

    if (build_snapshot_train) {
        repositories {
            mavenLocal()
            maven(url = "https://maven.pkg.jetbrains.space/kotlin/p/kotlin/dev")
        }
    }
}

plugins {
    id("org.jetbrains.kotlin.jvm") version "${extra["kotlin_version"]}"
}

repositories {
    maven(url = "https://maven.pkg.jetbrains.space/kotlin/p/kotlin/dev")
    mavenLocal()
    mavenCentral()
}

java {
    sourceCompatibility = JavaVersion.VERSION_1_8
    targetCompatibility = JavaVersion.VERSION_1_8
}

dependencies {
    testImplementation("org.jetbrains.kotlin:kotlin-test:${extra["kotlin_version"]}")
    testImplementation("org.ow2.asm:asm:${rootProject.properties["asm_version"]}")
    implementation("org.jetbrains.kotlin:kotlin-stdlib-jdk8")
}

sourceSets {
    // An assortment of tests for behavior of the core coroutines module on JVM
    jvmCoreTest {
        kotlin
        compileClasspath += sourceSets.test.runtimeClasspath
        runtimeClasspath += sourceSets.test.runtimeClasspath

        dependencies {
            implementation("org.jetbrains.kotlinx:kotlinx-coroutines-core:${rootProject.properties["coroutines_version"]}")
            implementation("com.google.guava:guava:31.1-jre")
        }
    }
    // Checks correctness of Maven publication (JAR resources) and absence of atomicfu symbols
    mavenTest {
        kotlin
        compileClasspath += sourceSets.test.runtimeClasspath
        runtimeClasspath += sourceSets.test.runtimeClasspath

        dependencies {
            implementation("org.jetbrains.kotlinx:kotlinx-coroutines-core:${rootProject.properties["coroutines_version"]}")
            implementation("org.jetbrains.kotlinx:kotlinx-coroutines-android:${rootProject.properties["coroutines_version"]}")
        }
    }
    // Checks that kotlinx-coroutines-debug can be used as -javaagent parameter
    debugAgentTest {
        kotlin
        compileClasspath += sourceSets.test.runtimeClasspath
        runtimeClasspath += sourceSets.test.runtimeClasspath

        dependencies {
            implementation("org.jetbrains.kotlinx:kotlinx-coroutines-core:${rootProject.properties["coroutines_version"]}")
            implementation("org.jetbrains.kotlinx:kotlinx-coroutines-debug:${rootProject.properties["coroutines_version"]}")
        }
    }

    // Checks that kotlinx-coroutines-debug agent can self-attach dynamically to JVM as a standalone dependency
    debugDynamicAgentTest {
        kotlin
        compileClasspath += sourceSets.test.runtimeClasspath
        runtimeClasspath += sourceSets.test.runtimeClasspath

        dependencies {
            implementation("org.jetbrains.kotlinx:kotlinx-coroutines-core:${rootProject.properties["coroutines_version"]}")
            implementation("org.jetbrains.kotlinx:kotlinx-coroutines-debug:${rootProject.properties["coroutines_version"]}")
        }
    }

    // Checks that kotlinx-coroutines-core can be used as -javaagent parameter
    coreAgentTest {
        kotlin
        compileClasspath += sourceSets.test.runtimeClasspath
        runtimeClasspath += sourceSets.test.runtimeClasspath

        dependencies {
            implementation("org.jetbrains.kotlinx:kotlinx-coroutines-core:${rootProject.properties["coroutines_version"]}")
        }
    }
}

compileDebugAgentTestKotlin {
    kotlinOptions {
        freeCompilerArgs += ["-Xallow-kotlin-package"]
    }
}

tasks.create<Test>("jvmCoreTest") {
    environment("version", rootProject.properties["coroutines_version"])
    val sourceSet = sourceSets.jvmCoreTest
    testClassesDirs = sourceSet.output.classesDirs
    classpath = sourceSet.runtimeClasspath
}

tasks.create<Test>("mavenTest") {
    environment("version", rootProject.properties["coroutines_version"])
    val sourceSet = sourceSets.mavenTest
    testClassesDirs = sourceSet.output.classesDirs
    classpath = sourceSet.runtimeClasspath
}

tasks.create<Test>("debugAgentTest") {
    val sourceSet = sourceSets.debugAgentTest
    val coroutinesDebugJar = sourceSet.runtimeClasspath.filter {it.name == "kotlinx-coroutines-debug-${coroutines_version}.jar" }.singleFile
    jvmArgs ("-javaagent:" + coroutinesDebugJar)
    testClassesDirs = sourceSet.output.classesDirs
    classpath = sourceSet.runtimeClasspath
    systemProperties(rootProject.properties.subMap(["overwrite.probes"]))
}

tasks.create<Test>("debugDynamicAgentTest") {
    val sourceSet = sourceSets.debugDynamicAgentTest
    testClassesDirs = sourceSet.output.classesDirs
    classpath = sourceSet.runtimeClasspath
}

tasks.create<Test>("coreAgentTest") {
    val sourceSet = sourceSets.coreAgentTest
    val coroutinesCoreJar = sourceSet.runtimeClasspath.filter {it.name == "kotlinx-coroutines-core-jvm-${coroutines_version}.jar" }.singleFile
    jvmArgs ("-javaagent:" + coroutinesCoreJar)
    testClassesDirs = sourceSet.output.classesDirs
    classpath = sourceSet.runtimeClasspath
}

compileTestKotlin {
    kotlinOptions.jvmTarget = "1.8"
}

check {
    dependsOn([jvmCoreTest, debugDynamicAgentTest, mavenTest, debugAgentTest, coreAgentTest, "smokeTest:build"])
}
compileKotlin {
    kotlinOptions {
        jvmTarget = "1.8"
    }
}
