/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

dependencies {
    implementation(project(":kotlinx-coroutines-reactive"))
}

tasks {
    compileKotlin {
        kotlinOptions.jvmTarget = "9"
    }

    compileTestKotlin {
        kotlinOptions.jvmTarget = "9"
    }
}

externalDocumentationLink(
    url = "https://docs.oracle.com/javase/9/docs/api/java/util/concurrent/Flow.html"
)
