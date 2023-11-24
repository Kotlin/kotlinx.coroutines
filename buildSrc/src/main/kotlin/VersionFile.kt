/*
 * Copyright 2016-2023 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

import org.gradle.api.*
import org.gradle.api.tasks.*

/**
 * Adds 'module_name.version' file to the project's JAR META-INF
 * for the better toolability. See #2941
 */
object VersionFile {
    fun registerVersionFileTask(project: Project): TaskProvider<Task> = with(project) {
        tasks.register("versionFileTask") {
            val name = project.name.replace('-', '_')
            val versionFile = project.layout.buildDirectory.file("$name.version")
            outputs.file(versionFile)
            doLast {
                versionFile.get().asFile.writeText(project.version.toString())
            }
        }
    }

    fun fromVersionFile(target: AbstractCopyTask, versionFileTask: TaskProvider<Task>) {
        target.from(versionFileTask) {
            into("META-INF")
        }
    }
}
