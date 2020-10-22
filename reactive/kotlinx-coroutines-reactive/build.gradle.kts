/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

val reactiveStreamsVersion = property("reactive_streams_version")

dependencies {
    jvmMainImplementation("org.reactivestreams:reactive-streams:$reactiveStreamsVersion")
    jvmTestImplementation("org.reactivestreams:reactive-streams-tck:$reactiveStreamsVersion")
}

val testNG by tasks.registering(Test::class) {
    useTestNG()
    val jvmTestTask = tasks.getByName("jvmTest") as Test
    classpath = jvmTestTask.classpath
    testClassesDirs = jvmTestTask.testClassesDirs
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

tasks.jvmTest {
    reports.html.destination = file("$buildDir/reports/junit")
}

tasks.check {
    dependsOn(testNG)
}

externalDocumentationLink(
    url = "https://www.reactive-streams.org/reactive-streams-$reactiveStreamsVersion-javadoc/"
)
