/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

val reactorVersion = version("reactor")

dependencies {
    compile("io.projectreactor:reactor-core:$reactorVersion")
    compile(project(":kotlinx-coroutines-reactive"))
}

java {
    targetCompatibility = JavaVersion.VERSION_1_8
    sourceCompatibility = JavaVersion.VERSION_1_8
}

tasks {
    compileKotlin {
        kotlinOptions.jvmTarget = "1.8"
    }

    compileTestKotlin {
        kotlinOptions.jvmTarget = "1.8"
    }
}

externalDocumentationLink(
    url = "https://projectreactor.io/docs/core/$reactorVersion/api/"
)
