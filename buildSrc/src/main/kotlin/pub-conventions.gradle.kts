import org.gradle.kotlin.dsl.*

/*
 * For some absolutely cursed reason the name 'publication-conventions' doesn't work in my IDE.
 * TODO: recheck after full repair
 */
plugins {
    id("maven-publish")
    id("signing")
}

apply(plugin = "maven-publish")
apply(plugin = "signing")

publishing {
    repositories {
        maven {
            name = "BuildLocal"
            url = uri(project.rootProject.layout.buildDirectory.dir("build-local-repository"))
        }
    }

    if (!isBom) {
        // Publish each JVM library under its project coordinates.
        apply(plugin = "java-library")

        // Include sources with the JVM publication.
        project.extensions.getByType(JavaPluginExtension::class.java).withSourcesJar()
        if (hasSharedSources) {
            val moduleDirectory = layout.projectDirectory.asFile
            tasks.named<Jar>("sourcesJar") {
                // Shared and JVM sources can have the same relative filename.
                // Preserve their directories so all implementations are included.
                eachFile {
                    path = file.relativeTo(moduleDirectory).invariantSeparatorsPath
                }
                includeEmptyDirs = false
            }
        }

        publications {
            register("mavenJava", MavenPublication::class) {
                from(components["java"])
            }
        }
    }

    val emptyJavadoc = if (!isBom) registerEmptyJavadocArtifact() else null
    publications.withType(MavenPublication::class).all {
        pom.configureMavenCentralMetadata(project)
        signPublicationIfKeyPresent(project, this)
        if (!isBom) {
            artifact(emptyJavadoc)
        }
    }

    project.establishSignDependencies()
}

// Compatibility with old TeamCity configurations that perform :kotlinx-coroutines-core:bintrayUpload
tasks.register("bintrayUpload") { dependsOn(tasks.matching { it.name == "publish" }) }

// Compatibility with old TeamCity configurations that perform `publishToMavenLocal`
tasks.named("publishToMavenLocal") {
    dependsOn(tasks.matching { it.name == "publishAllPublicationsToBuildLocalRepository" })
}
