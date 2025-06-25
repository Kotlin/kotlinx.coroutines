import java.net.*


plugins {
    id("org.jetbrains.dokka")
}

val knit_version: String by project
private val projectsWithoutDokka = unpublished + "kotlinx-coroutines-bom" + jdk8ObsoleteModule
private val subprojectWithDokka = subprojects.filterNot { projectsWithoutDokka.contains(it.name) }

configure(subprojectWithDokka) {
    apply(plugin = "org.jetbrains.dokka")
    configurePathsaver()
    configureDokkaTemplatesDir()
    condigureDokkaSetup()
}

// For top-level multimodule collection
configurePathsaver()
configureDokkaTemplatesDir()

dependencies {
    subprojectWithDokka.forEach {
        dokka(it)
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
        dokkaSourceSets.configureEach {
            jdkVersion = 11
            includes.from("README.md")
            sourceLink {
                localDirectory = rootDir
                remoteUrl("https://github.com/kotlin/kotlinx.coroutines/tree/master")
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
private fun Project.configureDokkaTemplatesDir() {
    dokka {
        pluginsConfiguration.html {
            templatesDir = rootDir.resolve("dokka-templates")
        }
    }
}
