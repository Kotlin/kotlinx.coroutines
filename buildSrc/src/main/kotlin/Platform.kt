/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

import org.gradle.api.Project

// Use from Groovy for now
fun platformOf(project: Project): String =
    when (project.name.substringAfterLast("-")) {
        "js" -> "js"
        "common", "native" -> throw IllegalStateException("${project.name} platform is not supported")
        else -> "jvm"
    }
