@file:Suppress("UnstableApiUsage")

import org.jetbrains.kotlin.gradle.tasks.*
import org.jetbrains.kotlin.gradle.dsl.JvmTarget

plugins {
    id("com.github.johnrengelman.shadow")
    id("me.champeau.jmh")
}

repositories {
    maven("https://repo.typesafe.com/typesafe/releases/")
}

java {
    sourceCompatibility = JavaVersion.VERSION_1_8
    targetCompatibility = JavaVersion.VERSION_1_8
}

tasks.named<KotlinCompile>("compileJmhKotlin") {
    compilerOptions {
        jvmTarget = JvmTarget.JVM_1_8
        freeCompilerArgs.add("-Xjvm-default=all")
    }
}

val jmhJarTask = tasks.named<Jar>("jmhJar") {
    archiveBaseName = "benchmarks"
    archiveClassifier = null
    archiveVersion = null
    archiveVersion.convention(null as String?)
    destinationDirectory = rootDir
}

tasks {
    // For some reason the DuplicatesStrategy from jmh is not enough
    // and errors with duplicates appear unless I force it to WARN only:
    withType<Copy> {
        duplicatesStrategy = DuplicatesStrategy.WARN
    }

    build {
        dependsOn(jmhJarTask)
    }
}

dependencies {
    implementation("org.openjdk.jmh:jmh-core:1.35")
    implementation("io.projectreactor:reactor-core:${version("reactor")}")
    implementation("io.reactivex.rxjava2:rxjava:2.1.9")
    implementation("com.github.akarnokd:rxjava2-extensions:0.20.8")

    implementation("com.typesafe.akka:akka-actor_2.12:2.5.0")
    implementation(project(":kotlinx-coroutines-core"))
    implementation(project(":kotlinx-coroutines-debug"))
    implementation(project(":kotlinx-coroutines-reactive"))

    // add jmh dependency on main
    "jmhImplementation"(sourceSets.main.get().runtimeClasspath)
}
