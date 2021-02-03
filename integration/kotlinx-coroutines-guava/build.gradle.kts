/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

val guavaVersion = "28.0-jre"

dependencies {
    compile("com.google.guava:guava:$guavaVersion")
}

externalDocumentationLink(
    url = "https://google.github.io/guava/releases/$guavaVersion/api/docs/"
)
