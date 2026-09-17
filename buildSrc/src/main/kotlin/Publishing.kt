@file:Suppress("UnstableApiUsage")

import org.gradle.api.Project
import org.gradle.api.publish.maven.*
import org.gradle.api.publish.maven.tasks.AbstractPublishToMaven
import org.gradle.api.tasks.*
import org.gradle.api.tasks.bundling.Jar
import org.gradle.kotlin.dsl.*
import org.gradle.plugins.signing.*

// Pom configuration

fun MavenPom.configureMavenCentralMetadata(project: Project) {
    name = project.name
    description = "Coroutines support libraries for Kotlin"
    url = "https://github.com/Kotlin/kotlinx.coroutines"

    licenses {
        license {
            name = "Apache-2.0"
            url = "https://www.apache.org/licenses/LICENSE-2.0.txt"
            distribution = "repo"
        }
    }

    developers {
        developer {
            id = "JetBrains"
            name = "JetBrains Team"
            organization = "JetBrains"
            organizationUrl = "https://www.jetbrains.com"
        }
    }

    scm {
        url = "https://github.com/Kotlin/kotlinx.coroutines"
    }
}

fun signPublicationIfKeyPresent(project: Project, publication: MavenPublication) {
    val keyId = project.getSensitiveProperty("libs.sign.key.id")
    val signingKey = project.getSensitiveProperty("libs.sign.key.private")
    val signingKeyPassphrase = project.getSensitiveProperty("libs.sign.passphrase")
    if (!signingKey.isNullOrBlank()) {
        project.extensions.configure<SigningExtension>("signing") {
            useInMemoryPgpKeys(keyId, signingKey, signingKeyPassphrase)
            sign(publication)
        }
    }
}

private fun Project.getSensitiveProperty(name: String): String? {
    return project.providers.gradleProperty(name).orNull ?: project.providers.environmentVariable(name).orNull
}

// Publishing must wait for signatures when signing is configured.
fun Project.establishSignDependencies() {
    tasks.withType<AbstractPublishToMaven>().configureEach {
        dependsOn(tasks.withType<Sign>())
    }
}

// Top-level deploy task that publishes all artifacts
public fun Project.registerTopLevelDeployTask() {
    assert(this === rootProject)
    tasks.register("deploy") {
        allprojects {
            val publishTasks = tasks.matching { it.name == "publish" }
            dependsOn(publishTasks)
        }
    }
}

public fun Project.registerEmptyJavadocArtifact(): TaskProvider<Jar> {
    return tasks.register("javadocJar", Jar::class) {
        archiveClassifier = "javadoc"
        // contents are deliberately left empty
    }
}

