/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

import org.jetbrains.dokka.DokkaConfiguration.ExternalDocumentationLink
import org.jetbrains.dokka.gradle.DokkaTask
import java.net.URL

val reactiveStreamsVersion = property("reactive_streams_version")

dependencies {
    compile("org.reactivestreams:reactive-streams:$reactiveStreamsVersion")
    testCompile("org.reactivestreams:reactive-streams-tck:$reactiveStreamsVersion")
}

tasks {
    val testNG = register<Test>("testNG") {
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

    named<Test>("test") {
        reports.html.destination = file("$buildDir/reports/junit")

        dependsOn(testNG)
    }

    withType<DokkaTask>().configureEach {
        externalDocumentationLink(delegateClosureOf<ExternalDocumentationLink.Builder> {
            url = URL("https://www.reactive-streams.org/reactive-streams-$reactiveStreamsVersion-javadoc/")
            packageListUrl = projectDir.toPath().resolve("package.list").toUri().toURL()
        })
    }
}
