/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

import org.gradle.api.JavaVersion

if (!JavaVersion.current().isJava11Compatible) {
    val message = "Project required JDK 11+, but found ${JavaVersion.current()}"
    if (Idea.active) {
        logger.error(message)
    } else {
        throw GradleException(message)
    }
}
