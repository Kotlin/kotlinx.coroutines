/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

val guavaVersion = "31.0.1-jre"

dependencies {
    api("com.google.guava:guava:$guavaVersion")
}

java {
    targetCompatibility = JavaVersion.VERSION_1_8
    sourceCompatibility = JavaVersion.VERSION_1_8
}

externalDocumentationLink(
    url = "https://google.github.io/guava/releases/$guavaVersion/api/docs/"
)
