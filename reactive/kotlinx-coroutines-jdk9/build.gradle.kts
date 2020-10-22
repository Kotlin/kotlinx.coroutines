/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

dependencies {
    jvmMainImplementation(project(":kotlinx-coroutines-reactive"))
    jvmMainImplementation("org.reactivestreams:reactive-streams-flow-adapters:${version("reactive_streams")}")
}

kotlin {
    val targets = if (rootProject.ext.get("build_snapshot_train") as Boolean) {
        listOf(jvm("jvm"), jvm("jvmIr"))
    } else {
        listOf(jvm("jvm"))
    }
    configure(targets) {
        compilations.all {
            kotlinOptions.jvmTarget = "9"
        }
    }
}

externalDocumentationLink(
    url = "https://docs.oracle.com/javase/9/docs/api/java/util/concurrent/Flow.html"
)
