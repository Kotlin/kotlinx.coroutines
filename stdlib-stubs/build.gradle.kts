/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

kotlin {
    val targets = if (rootProject.ext.get("jvm_ir_target_enabled") as Boolean) {
        listOf(jvm("jvm"), jvm("jvmIr"))
    } else {
        listOf(jvm("jvm"))
    }
    configure(targets) {
        val main by compilations.getting {
            kotlinOptions.freeCompilerArgs += "-Xallow-kotlin-package"
        }
    }
}
