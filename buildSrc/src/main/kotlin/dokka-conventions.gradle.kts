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

// Setup top-level 'dokkaHtmlMultiModule' with templates
tasks.withType<DokkaMultiModuleTask>().named("dokkaHtmlMultiModule") {
    setupDokkaTemplatesDir(this)
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
        setupDokkaTemplatesDir(this)

        dokkaSourceSets.configureEach {
            jdkVersion = 11
            includes.from("README.md")
            noStdlibLink = true

            externalDocumentationLink {
                url = URL("https://kotlinlang.org/api/latest/jvm/stdlib/")
                packageListUrl = rootProject.projectDir.toPath().resolve("site/stdlib.package.list").toUri().toURL()
            }

            // Something suspicious to figure out, probably legacy of earlier days
            if (!project.isMultiplatform) {
                dependsOn(project.configurations["compileClasspath"])
            }
        }

        // Source links
        dokkaSourceSets.configureEach {
            sourceLink {
                localDirectory = rootDir
                remoteUrl = URL("https://github.com/kotlin/kotlinx.coroutines/tree/master")
                remoteLineSuffix ="#L"
            }
        }
    }
}

private fun Project.configureExternalLinks() {
    tasks.withType<DokkaTaskPartial>() {
        dokkaSourceSets.configureEach {
            externalDocumentationLink {
                url = URL(coreModuleDocsUrl)
                packageListUrl = File(coreModuleDocsPackageList).toURI().toURL()
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
private fun Project.setupDokkaTemplatesDir(dokkaTask: AbstractDokkaTask) {
    dokkaTask.pluginsMapConfiguration = mapOf(
        "org.jetbrains.dokka.base.DokkaBase" to """{ "templatesDir" : "${
            project.rootProject.projectDir.toString().replace('\\', '/')
        }/dokka-templates" }"""
    )
}
