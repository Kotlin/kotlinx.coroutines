import kotlinx.kover.gradle.plugin.dsl.*

/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

plugins {
    // apply plugin to use autocomplete for Kover DSL
    id("org.jetbrains.kotlinx.kover")
}

val reactiveStreamsVersion = property("reactive_streams_version")

dependencies {
    api("org.reactivestreams:reactive-streams:$reactiveStreamsVersion")
    testImplementation("org.reactivestreams:reactive-streams-tck:$reactiveStreamsVersion")
}

val testNG by tasks.registering(Test::class) {
    useTestNG()
    reports.html.destination = file("$buildDir/reports/testng")
    include("**/*ReactiveStreamTckTest.*")
    // Skip testNG when tests are filtered with --tests, otherwise it simply fails
    onlyIf {
        filter.includePatterns.isEmpty()
    }
    doFirst {
        // Classic gradle, nothing works without doFirst
        println("TestNG tests: ($includes)")
    }
}

tasks.test {
    reports.html.destination = file("$buildDir/reports/junit")
}

tasks.check {
    dependsOn(testNG)
}

externalDocumentationLink(
    url = "https://www.reactive-streams.org/reactive-streams-$reactiveStreamsVersion-javadoc/"
)

koverReport {
    filters {
        excludes {
            className(
                "kotlinx.coroutines.reactive.FlowKt", // Deprecated
                "kotlinx.coroutines.reactive.FlowKt__MigrationKt", // Deprecated
                "kotlinx.coroutines.reactive.ConvertKt" // Deprecated
            )
        }
    }
}
