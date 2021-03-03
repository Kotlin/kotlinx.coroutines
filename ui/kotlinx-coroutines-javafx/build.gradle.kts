/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

plugins {
    id("org.openjfx.javafxplugin") version "0.0.9"
}

javafx {
    version = version("javafx")
    modules = listOf("javafx.controls")
    configuration = "compileOnly"
}

sourceSets {
    test.configure {
        compileClasspath += configurations.compileOnly
        runtimeClasspath += configurations.compileOnly
    }
}

val JDK_18: String? by lazy {
    System.getenv("JDK_18")
}

val checkJdk8 by tasks.registering {
    // only fail w/o JDK_18 when actually trying to test, not during project setup phase
    doLast {
        if (JDK_18 == null) {
            throw GradleException(
                """
                JDK_18 environment variable is not defined.
                Can't run JDK 8 compatibility tests.
                Please ensure JDK 8 is installed and that JDK_18 points to it.
                """.trimIndent()
            )
        }
    }
}

val jdk8Test by tasks.registering(Test::class) {
    // Run these tests only during nightly stress test
    onlyIf { project.properties["stressTest"] != null }

    val test = tasks.test.get()

    classpath = test.classpath
    testClassesDirs = test.testClassesDirs
    executable = "$JDK_18/bin/java"

    dependsOn("compileTestKotlin")
    dependsOn(checkJdk8)
}

tasks.build {
    dependsOn(jdk8Test)
}
