/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

dependencies {
    implementation("io.github.microutils:kotlin-logging-jvm:2.1.17")
    implementation(project(":kotlinx-coroutines-slf4j"))
    val log4JVersion = "2.16.0"
    testImplementation("org.apache.logging.log4j:log4j-core:$log4JVersion")
    testRuntimeOnly("org.apache.logging.log4j:log4j-slf4j-impl:$log4JVersion")
}
