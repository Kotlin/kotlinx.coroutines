/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

import org.gradle.api.*
import org.gradle.kotlin.dsl.*
import org.jetbrains.dokka.gradle.*
import java.io.*
import java.net.*

/**
 * Package-list by external URL for documentation generation.
 */
fun Project.externalDocumentationLink(
    url: String,
    packageList: File = projectDir.resolve("package.list")
) {
    tasks.withType<AbstractDokkaLeafTask>().configureEach {
        dokkaSourceSets.configureEach {
            externalDocumentationLink {
                this.url.set(URL(url))
                packageListUrl.set(packageList.toPath().toUri().toURL())
            }
        }
    }
}
