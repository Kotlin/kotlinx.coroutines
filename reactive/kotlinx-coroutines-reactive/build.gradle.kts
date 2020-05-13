/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

val reactiveStreamsVersion = property("reactive_streams_version")

dependencies {
    compile("org.reactivestreams:reactive-streams:$reactiveStreamsVersion")
    testCompile("org.reactivestreams:reactive-streams-tck:$reactiveStreamsVersion")
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

    dependsOn(testNG)
}

externalDocumentationLink(
    url = "https://www.reactive-streams.org/reactive-streams-$reactiveStreamsVersion-javadoc/"
)
