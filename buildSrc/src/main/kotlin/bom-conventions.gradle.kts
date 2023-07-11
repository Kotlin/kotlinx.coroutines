/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
import org.gradle.kotlin.dsl.*
import org.jetbrains.kotlin.gradle.dsl.*


configure(subprojects.filter { it.name !in unpublished }) {
    if (name == "kotlinx-coroutines-bom" || name == "kotlinx.coroutines") return@configure
    if (isMultiplatform) {
        kotlinExtension.sourceSets.getByName("jvmMain").dependencies {
            api(project.dependencies.platform(project(":kotlinx-coroutines-bom")))
        }
    } else {
        dependencies {
            "api"(platform(project(":kotlinx-coroutines-bom")))
        }
    }
}
