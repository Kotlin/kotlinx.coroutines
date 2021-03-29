/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

import org.gradle.api.Project
import org.gradle.kotlin.dsl.delegateClosureOf
import org.gradle.kotlin.dsl.withType
import org.jetbrains.dokka.DokkaConfiguration.ExternalDocumentationLink.Builder
import org.jetbrains.dokka.gradle.DokkaTask
import java.io.File
import java.net.URL

/**
 * Package-list by external URL for documentation generation.
 */
fun Project.externalDocumentationLink(
    url: String,
    packageList: File = projectDir.resolve("package.list")
) {
    tasks.withType<DokkaTask>().configureEach {
        externalDocumentationLink(delegateClosureOf<Builder> {
            this.url = URL(url)
            packageListUrl = packageList.toPath().toUri().toURL()
        })
    }
}
