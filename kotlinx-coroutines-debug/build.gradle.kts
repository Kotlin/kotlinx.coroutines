/*
 * Copyright 2016-2023 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

import com.github.jengelman.gradle.plugins.shadow.tasks.*

plugins {
   id("com.github.johnrengelman.shadow")
   id("org.jetbrains.kotlinx.kover") // apply plugin to use autocomplete for Kover DSL
}

configurations{
  val shadowDeps by creating
  compileOnly.configure {
    extendsFrom(shadowDeps)
  }
  runtimeOnly.configure {
    extendsFrom(shadowDeps)
  }
}

val junit_version by properties
val junit5_version by properties
val byte_buddy_version by properties
val blockhound_version by properties
val jna_version by properties

dependencies {
    compileOnly("junit:junit:$junit_version")
    compileOnly("org.junit.jupiter:junit-jupiter-api:$junit5_version")
    testImplementation("org.junit.jupiter:junit-jupiter-engine:$junit5_version")
    testImplementation("org.junit.platform:junit-platform-testkit:1.7.0")
    add("shadowDeps", "net.bytebuddy:byte-buddy:$byte_buddy_version")
    add("shadowDeps", "net.bytebuddy:byte-buddy-agent:$byte_buddy_version")
    compileOnly("io.projectreactor.tools:blockhound:$blockhound_version")
    testImplementation("io.projectreactor.tools:blockhound:$blockhound_version")
    testImplementation("com.google.code.gson:gson:2.8.6")
    api("net.java.dev.jna:jna:$jna_version")
    api("net.java.dev.jna:jna-platform:$jna_version")
}

java {
    /* This is needed to be able to run JUnit5 tests. Otherwise, Gradle complains that it can't find the
    JVM1.6-compatible version of the `junit-jupiter-api` artifact. */
    disableAutoTargetJvm()
}

// This is required for BlockHound tests to work, see https://github.com/Kotlin/kotlinx.coroutines/issues/3701
tasks.withType<Test>().configureEach {
    if (JavaVersion.current().isCompatibleWith(JavaVersion.VERSION_13)) {
        jvmArgs("-XX:+AllowRedefinitionToAddDeleteMethods")
    }
}

val jar by tasks.getting(Jar::class) {
    enabled = false
}

val versionFileTask = VersionFile.registerVersionFileTask(project)

val shadowJar by tasks.getting(ShadowJar::class) {
    // Shadow only byte buddy, do not package kotlin stdlib
    configurations = listOf(project.configurations["shadowDeps"])
    relocate("net.bytebuddy", "kotlinx.coroutines.repackaged.net.bytebuddy") {
        this.exclude("META-INF/versions/9/module-info.class")
    }
    // // exclude the module-info.class provided by bytebuddy
    // exclude("META-INF/versions/9/module-info.class")
    archiveClassifier.convention(null as String?)
    archiveClassifier.set(null as String?)
    archiveBaseName.set(jar.archiveBaseName)
    archiveVersion.set(jar.archiveVersion)
    manifest {
        attributes(mapOf(
            "Premain-Class" to "kotlinx.coroutines.debug.AgentPremain",
            "Can-Redefine-Classes" to "true",
            "Multi-Release" to "true"
        ))
    }
    VersionFile.fromVersionFile(this, versionFileTask)
    from(tasks.compileModuleInfoJava) {
        // Include **only** file we are interested in as JavaCompile output also contains some tmp files
        include("module-info.class")
        into("META-INF/versions/9/")
    }
    duplicatesStrategy = DuplicatesStrategy.FAIL
}

configurations {
    // shadowJar is already part of the `shadowRuntimeElements` and `shadowApiElements`, but it's not enough.
    artifacts {
        add("apiElements", shadowJar)
        add("runtimeElements", shadowJar)
    }
}

koverReport {
    filters {
        excludes {
            // Never used, safety mechanism
            classes("kotlinx.coroutines.debug.internal.NoOpProbesKt")
        }
    }
}
