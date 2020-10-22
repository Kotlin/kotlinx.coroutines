/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

val reactorVersion = version("reactor")

dependencies {
    jvmMainImplementation("io.projectreactor:reactor-core:$reactorVersion")
    jvmMainImplementation(project(":kotlinx-coroutines-reactive"))
}

kotlin {
    configure(listOf(jvm("jvm"), jvm("jvmIr"))) {
        compilations.all {
            kotlinOptions.jvmTarget = "1.8"
        }
    }
}

externalDocumentationLink(
    url = "https://projectreactor.io/docs/core/$reactorVersion/api/"
)
