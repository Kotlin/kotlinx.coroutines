/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

dependencies {
    jvmMainImplementation("org.slf4j:slf4j-api:1.7.25")
    jvmTestImplementation("io.github.microutils:kotlin-logging:1.5.4")
    jvmTestRuntime("ch.qos.logback:logback-classic:1.2.3")
    jvmTestRuntime("ch.qos.logback:logback-core:1.2.3")
}

externalDocumentationLink(
    url = "https://www.slf4j.org/apidocs/"
)
