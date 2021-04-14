/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

import org.gradle.api.Project

fun Project.version(target: String): String =
    property("${target}_version") as String
