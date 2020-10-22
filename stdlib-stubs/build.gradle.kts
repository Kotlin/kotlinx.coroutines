/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

import org.jetbrains.kotlin.gradle.tasks.KotlinCompile

kotlin {
    configure(listOf(jvm())) {
        val main by compilations.getting {
            kotlinOptions.freeCompilerArgs += "-Xallow-kotlin-package"
        }
    }
}
