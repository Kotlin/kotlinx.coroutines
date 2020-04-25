/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

import org.jetbrains.kotlin.gradle.tasks.KotlinCompile

plugins {
    id("net.ltgt.apt")
    id("com.github.johnrengelman.shadow")
    id("me.champeau.gradle.jmh")
}

repositories {
    maven("https://repo.typesafe.com/typesafe/releases/")
}

tasks.withType<KotlinCompile>().configureEach {
    kotlinOptions.jvmTarget = "1.8"
}

tasks.compileJmhKotlin {
    kotlinOptions.freeCompilerArgs += "-Xjvm-default=enable"
}

/*
 * Due to a bug in the inliner it sometimes does not remove inlined symbols (that are later renamed) from unused code paths,
 * and it breaks JMH that tries to post-process these symbols and fails because they are renamed.
 */
val removeRedundantFiles = tasks.register<Delete>("removeRedundantFiles") {
    delete("$buildDir/classes/kotlin/jmh/benchmarks/flow/scrabble/FlowPlaysScrabbleOpt\$play\$buildHistoOnScore\$1\$\$special\$\$inlined\$filter\$1\$1.class")
    delete("$buildDir/classes/kotlin/jmh/benchmarks/flow/scrabble/FlowPlaysScrabbleOpt\$play\$nBlanks\$1\$\$special\$\$inlined\$map\$1\$1.class")
    delete("$buildDir/classes/kotlin/jmh/benchmarks/flow/scrabble/FlowPlaysScrabbleOpt\$play\$score2\$1\$\$special\$\$inlined\$map\$1\$1.class")
    delete("$buildDir/classes/kotlin/jmh/benchmarks/flow/scrabble/FlowPlaysScrabbleOpt\$play\$bonusForDoubleLetter\$1\$\$special\$\$inlined\$map\$1\$1.class")
    delete("$buildDir/classes/kotlin/jmh/benchmarks/flow/scrabble/FlowPlaysScrabbleOpt\$play\$nBlanks\$1\$\$special\$\$inlined\$map\$1\$2\$1.class")
    delete("$buildDir/classes/kotlin/jmh/benchmarks/flow/scrabble/FlowPlaysScrabbleOpt\$play\$bonusForDoubleLetter\$1\$\$special\$\$inlined\$map\$1\$2\$1.class")
    delete("$buildDir/classes/kotlin/jmh/benchmarks/flow/scrabble/FlowPlaysScrabbleOpt\$play\$score2\$1\$\$special\$\$inlined\$map\$1\$2\$1.class")
    delete("$buildDir/classes/kotlin/jmh/benchmarks/flow/scrabble/FlowPlaysScrabbleOptKt\$\$special\$\$inlined\$collect\$1\$1.class")
    delete("$buildDir/classes/kotlin/jmh/benchmarks/flow/scrabble/FlowPlaysScrabbleOptKt\$\$special\$\$inlined\$collect\$2\$1.class")
    delete("$buildDir/classes/kotlin/jmh/benchmarks/flow/scrabble/FlowPlaysScrabbleOpt\$play\$histoOfLetters\$1\$\$special\$\$inlined\$fold\$1\$1.class")
    delete("$buildDir/classes/kotlin/jmh/benchmarks/flow/scrabble/FlowPlaysScrabbleBase\$play\$buildHistoOnScore\$1\$\$special\$\$inlined\$filter\$1\$1.class")
    delete("$buildDir/classes/kotlin/jmh/benchmarks/flow/scrabble/FlowPlaysScrabbleBase\$play\$histoOfLetters\$1\$\$special\$\$inlined\$fold\$1\$1.class")
    delete("$buildDir/classes/kotlin/jmh/benchmarks/flow/scrabble//SaneFlowPlaysScrabble\$play\$buildHistoOnScore\$1\$\$special\$\$inlined\$filter\$1\$1.class")

    // Primes
    delete("$buildDir/classes/kotlin/jmh/benchmarks/flow/misc/Numbers\$\$special\$\$inlined\$filter\$1\$2\$1.class")
    delete("$buildDir/classes/kotlin/jmh/benchmarks/flow/misc/Numbers\$\$special\$\$inlined\$filter\$1\$1.class")
}

tasks.jmhRunBytecodeGenerator {
    dependsOn(removeRedundantFiles)
}

// It is better to use the following to run benchmarks, otherwise you may get unexpected errors:
// ./gradlew --no-daemon cleanJmhJar jmh -Pjmh="MyBenchmark"
jmh {
    jmhVersion = "1.21"
    duplicateClassesStrategy = DuplicatesStrategy.INCLUDE
    failOnError = true
    resultFormat = "CSV"
    project.findProperty("jmh")?.also {
        include = listOf(".*$it.*")
    }
//    includeTests = false
}

tasks.jmhJar {
    baseName = "benchmarks"
    classifier = null
    version = null
    destinationDir = file("$rootDir")
}

dependencies {
    compile("org.openjdk.jmh:jmh-core:1.21")
    compile("io.projectreactor:reactor-core:${property("reactor_vesion")}")
    compile("io.reactivex.rxjava2:rxjava:2.1.9")
    compile("com.github.akarnokd:rxjava2-extensions:0.20.8")

    compile("org.openjdk.jmh:jmh-core:1.21")
    compile("com.typesafe.akka:akka-actor_2.12:2.5.0")
    compile(project(":kotlinx-coroutines-core"))

    // add jmh dependency on main
    jmhImplementation(sourceSets.main.get().runtimeClasspath)
}
