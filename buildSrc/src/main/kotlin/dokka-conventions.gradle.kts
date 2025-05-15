import org.gradle.api.Project
import org.jetbrains.dokka.gradle.*
import java.io.File
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

// For top-level multimodule collection
dokka {
    setupDokkaTemplatesDir()
}
dependencies {
    dokkaPlugin("org.jetbrains.kotlinx:dokka-pathsaver-plugin:$knit_version")

    subprojects.forEach {
        if (it.name !in projetsWithoutDokka) {
            dokka(it)
        }
    }
}

// Dependencies for Knit processing: Knit plugin to work with Dokka
private fun Project.configurePathsaver() {
    dependencies {
        dokkaPlugin("org.jetbrains.kotlinx:dokka-pathsaver-plugin:$knit_version")
    }
}

// Configure Dokka setup
private fun Project.condigureDokkaSetup() {
    dokka {
        dokkaPublications.configureEach {
            suppressInheritedMembers = true
        }

        setupDokkaTemplatesDir()

        dokkaSourceSets.configureEach {
            jdkVersion = 11
            includes.from("README.md")
            sourceLink {
                localDirectory = rootDir
                remoteUrl = URI("https://github.com/kotlin/kotlinx.coroutines/tree/master")
            }
        }
    }
}

private fun Project.configureExternalLinks() {
    dokka {
        dokkaSourceSets.configureEach {
            externalDocumentationLinks.register("kotlinx-coroutines-core") {
                url = URI(coreModuleDocsUrl)
                packageListUrl = File(coreModuleDocsPackageList).toURI()
            }
        }
    }
}

/**
 * Setups Dokka templates. While this directory is empty in our repository,
 * 'kotlinlang' build pipeline adds templates there when preparing our documentation
 * to be published on kotlinlang.
 *
 * See:
 * - Template setup: https://github.com/JetBrains/kotlin-web-site/blob/master/.teamcity/builds/apiReferences/kotlinx/coroutines/KotlinxCoroutinesPrepareDokkaTemplates.kt
 * - Templates repository: https://github.com/JetBrains/kotlin-web-site/tree/master/dokka-templates
 */
private fun DokkaExtension.setupDokkaTemplatesDir() {
    pluginsConfiguration.html {
        templatesDir = rootDir.resolve("dokka-templates")
    }
}
