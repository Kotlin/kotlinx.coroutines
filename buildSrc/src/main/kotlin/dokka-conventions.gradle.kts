/*
 * Copyright 2016-2023 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

import org.jetbrains.dokka.gradle.*
import java.net.*


plugins {
    id("org.jetbrains.dokka")
}

val knit_version: String by project
private val projetsWithoutDokka = unpublished + "kotlinx-coroutines-bom" + jdk8ObsoleteModule
private val coreModuleDocsUrl = "https://kotlinlang.org/api/kotlinx.coroutines/$coreModule/"
private val coreModuleDocsPackageList = "$projectDir/kotlinx-coroutines-core/build/dokka/htmlPartial/package-list"

configure(subprojects.filterNot { projetsWithoutDokka.contains(it.name) }) {
    apply(plugin = "org.jetbrains.dokka")
    configurePathsaver()
    condigureDokkaSetup()
    configureExternalLinks()
}

// Setup top-level 'dokkaHtmlMultiModule' with the same suspicious template setup
tasks.withType<DokkaMultiModuleTask>().named("dokkaHtmlMultiModule") {
    pluginsMapConfiguration = mapOf(
        "org.jetbrains.dokka.base.DokkaBase" to """{ "templatesDir" : "${
            rootProject.projectDir.toString().replace('\\', '/')
        }/dokka-templates" }"""
    )
}

dependencies {
    // Add explicit dependency between Dokka and Knit plugin
    add("dokkaHtmlMultiModulePlugin", "org.jetbrains.kotlinx:dokka-pathsaver-plugin:$knit_version")
}

// Dependencies for Knit processing: Knit plugin to work with Dokka
private fun Project.configurePathsaver() {
    tasks.withType(DokkaTaskPartial::class).configureEach {
        dependencies {
            plugins("org.jetbrains.kotlinx:dokka-pathsaver-plugin:$knit_version")
        }
    }
}

// Configure Dokka setup
private fun Project.condigureDokkaSetup() {
    tasks.withType(DokkaTaskPartial::class).configureEach {
        suppressInheritedMembers = true
        // Something suspicious to figure out
        pluginsMapConfiguration = mapOf(
            "org.jetbrains.dokka.base.DokkaBase" to """{ "templatesDir" : "${
                rootProject.projectDir.toString().replace('\\', '/')
            }/dokka-templates" }"""
        )

        dokkaSourceSets.configureEach {
            jdkVersion.set(11)
            includes.from("README.md")
            noStdlibLink.set(true)

            externalDocumentationLink {
                url.set(URL("https://kotlinlang.org/api/latest/jvm/stdlib/"))
                packageListUrl.set(rootProject.projectDir.toPath().resolve("site/stdlib.package.list").toUri().toURL())
            }

            // Something suspicious to figure out, probably legacy of earlier days
            if (!project.isMultiplatform) {
                dependsOn(project.configurations["compileClasspath"])
            }
        }

        // Source links
        dokkaSourceSets.configureEach {
            sourceLink {
                localDirectory.set(rootDir)
                remoteUrl.set(URL("https://github.com/kotlin/kotlinx.coroutines/tree/master"))
                remoteLineSuffix.set("#L")
            }
        }
    }
}

private fun Project.configureExternalLinks() {
    tasks.withType<DokkaTaskPartial>() {
        dokkaSourceSets.configureEach {
            externalDocumentationLink {
                url.set(URL(coreModuleDocsUrl))
                packageListUrl.set(File(coreModuleDocsPackageList).toURI().toURL())
            }
        }
    }
}
