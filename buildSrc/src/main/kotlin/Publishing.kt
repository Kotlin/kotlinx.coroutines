/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("UnstableApiUsage")

import org.gradle.api.Project
import org.gradle.api.artifacts.dsl.*
import org.gradle.api.publish.maven.*
import org.gradle.kotlin.dsl.*
import org.gradle.plugins.signing.*
import java.net.*

// Pom configuration

fun MavenPom.configureMavenCentralMetadata(project: Project) {
    name by project.name
    description by "Coroutines support libraries for Kotlin"
    url by "https://github.com/Kotlin/kotlinx.coroutines"

    licenses {
        license {
            name by "The Apache Software License, Version 2.0"
            url by "https://www.apache.org/licenses/LICENSE-2.0.txt"
            distribution by "repo"
        }
    }

    developers {
        developer {
            id by "JetBrains"
            name by "JetBrains Team"
            organization by "JetBrains"
            organizationUrl by "https://www.jetbrains.com"
        }
    }

    scm {
        url by "https://github.com/Kotlin/kotlinx.coroutines"
    }
}

fun configureMavenPublication(rh: RepositoryHandler, project: Project) {
    rh.maven {
        url = URI("https://maven.pkg.jetbrains.space/kotlin/p/wasm/experimental")
        credentials {
            username = project.getSensitiveProperty("kotlin.space.packages.wasm.user")
            password = project.getSensitiveProperty("kotlin.space.packages.wasm.secret")
        }
    }

    // Something that's easy to "clean" for development, not mavenLocal
    rh.maven("${project.rootProject.buildDir}/repo") {
        name = "buildRepo"
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
    return project.findProperty(name) as? String ?: System.getenv(name)
}
