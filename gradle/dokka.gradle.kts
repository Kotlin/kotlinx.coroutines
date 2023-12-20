import org.jetbrains.dokka.gradle.*
import java.net.*

/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

// Configures generation of JavaDoc & Dokka artifacts
apply<DokkaPlugin>()
//apply<JavaPlugin>()


val knit_version: String by project
tasks.withType(DokkaTaskPartial::class).configureEach {
    dependencies {
        plugins("org.jetbrains.kotlinx:dokka-pathsaver-plugin:$knit_version")
    }
}

tasks.withType(DokkaTaskPartial::class).configureEach {
    suppressInheritedMembers.set(true)
    pluginsMapConfiguration.set(mapOf("org.jetbrains.dokka.base.DokkaBase" to """{ "templatesDir" : "${rootProject.projectDir.toString().replace('\\', '/')}/dokka-templates" }"""))

    dokkaSourceSets.configureEach {
        jdkVersion.set(11)
        includes.from("README.md")
        noStdlibLink.set(true)

        externalDocumentationLink {
            url.set(URL("https://kotlinlang.org/api/latest/jvm/stdlib/"))
            packageListUrl.set(rootProject.projectDir.toPath().resolve("site/stdlib.package.list").toUri().toURL())
        }

        if (!project.isMultiplatform) {
            dependsOn(project.configurations["compileClasspath"])
        }
    }
}

tasks.withType(DokkaTaskPartial::class).configureEach {
    dokkaSourceSets.configureEach {
        sourceLink {
            localDirectory.set(rootDir)
            remoteUrl.set(URL("https://github.com/kotlin/kotlinx.coroutines/tree/master"))
            remoteLineSuffix.set("#L")
        }
    }
}
