/*
 * Copyright 2016-2023 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

import org.gradle.api.*
import org.gradle.api.tasks.*
import org.gradle.kotlin.dsl.*

object VersionFile {
    fun configure(project: Project, jarTask: AbstractCopyTask) = with(project) {
        val versionFileTask by tasks.register("versionFileTask") {
            val name = project.name.replace('-', '_')
            val versionFile = project.layout.buildDirectory.file("$name.version")
            outputs.file(versionFile)
            doLast {
                versionFile.get().asFile.writeText(project.version.toString())
            }
        }
        jarTask.dependsOn(versionFileTask)
        jarTask.from(versionFileTask) {
            into("META-INF")
        }
    }
}
