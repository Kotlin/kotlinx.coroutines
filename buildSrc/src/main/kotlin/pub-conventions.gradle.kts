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
        configureMavenPublication(this, project)
    }

    if (!isMultiplatform && !isBom) {
        // Configure java publications for regular non-MPP modules
        apply(plugin = "java-library")

        // MPP projects pack their sources automatically, java libraries need to explicitly pack them
        val sources = tasks.register("sourcesJar", Jar::class) {
            archiveClassifier = "sources"
            from(sourceSets.named("main").get().allSource)
        }

        publications {
            register("mavenJava", MavenPublication::class) {
                from(components["java"])
                artifact(sources)
            }
        }
    }

    val emptyJavadoc = if (!isBom) registerEmptyJavadocArtifact() else null
    publications.withType(MavenPublication::class).all {
        pom.configureMavenCentralMetadata(project)
        signPublicationIfKeyPresent(project, this)
        if (!isBom && name != "kotlinMultiplatform") {
            artifact(emptyJavadoc)
        }

        val type = name
        when (type) {
            "kotlinMultiplatform" -> {
                // With Kotlin 1.4 & HMPP, the root module should have no suffix in the ID, but for compatibility with
                // the consumers who can't read Gradle module metadata, we publish the JVM artifacts in it, too
                artifactId = project.name
                project.reconfigureMultiplatformPublication(publications.getByName("jvm") as MavenPublication)
            }

            "metadata", "jvm", "js", "native" -> {
                artifactId = "${project.name}-$type"
            }
        }
    }

    project.establishSignDependencies()
}


// Legacy from https://github.com/Kotlin/kotlinx.coroutines/pull/2031
// Should be fixed with the rest of the hacks around publication
tasks.matching { it.name == "generatePomFileForKotlinMultiplatformPublication" }.configureEach {
    dependsOn(tasks.matching { it.name == "generatePomFileForJvmPublication" })
}

// Compatibility with old TeamCity configurations that perform :kotlinx-coroutines-core:bintrayUpload
tasks.register("bintrayUpload") { dependsOn(tasks.matching { it.name == "publish" }) }
