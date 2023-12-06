/*
 * Copyright 2016-2023 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

plugins {
    id("kotlinx-knit")
}

knit {
    siteRoot = "https://kotlinlang.org/api/kotlinx.coroutines"
    moduleRoots = listOf(".", "integration", "reactive", "ui")
    moduleDocs = "build/dokka/htmlPartial"
    dokkaMultiModuleRoot = "build/dokka/htmlMultiModule/"
}

tasks.named("knitPrepare").configure {
    val knitTask = this
    // In order for knit to operate, it should depend on and collect
    // all Dokka outputs from each module
    allprojects {
        val dokkaTasks = tasks.matching { it.name == "dokkaHtmlMultiModule" }
        knitTask.dependsOn(dokkaTasks)
    }
}
