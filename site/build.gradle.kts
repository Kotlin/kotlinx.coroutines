import groovy.lang.*

/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

val buildDocsDir = "$buildDir/docs"
val jekyllDockerImage = "jekyll/jekyll:${version("jekyll")}"

val copyDocs = tasks.register<Copy>("copyDocs") {
    val dokkaTasks = rootProject.getTasksByName("dokka", true)

    from(dokkaTasks.map { "${it.project.buildDir}/dokka" }) {
        include("**/*.md")
        include("**/package-list")
    }
    from("docs")
    into(buildDocsDir)
    filter { it.replace("/index.md\"", "/index.html\"") }

    dependsOn(dokkaTasks)
}

val copyExampleFrontendJs = tasks.register<Copy>("copyExampleFrontendJs") {
    val srcBuildDir = project(":example-frontend-js").buildDir
    from("$srcBuildDir/dist")
    into("$buildDocsDir/example-frontend-js")

    dependsOn(":example-frontend-js:bundle")
}

tasks.register<Exec>("site") {
    description = "Generate github pages"

    inputs.files(fileTree(buildDocsDir))
    outputs.dir("$buildDir/dist")
    workingDir = file(buildDocsDir)

    commandLine(
        "docker", "run", "--rm", "--volume=$buildDir:/srv/jekyll",
        "-t", jekyllDockerImage,
        "/bin/bash", "-c", "cd docs; jekyll build"
    )

    dependsOn(copyDocs)
    dependsOn(copyExampleFrontendJs)
}

// A useful task for local debugging -- serves a site locally
tasks.register<Exec>("serve") {
    commandLine(
        "docker", "run", "--rm", "--volume=$buildDir:/srv/jekyll",
        "-p", "8080:8080",
        "-t", jekyllDockerImage,
        "/bin/bash", "-c", "cd docs; jekyll serve --host 0.0.0.0 --port 8080"
    )

    dependsOn(copyDocs)
    dependsOn(copyExampleFrontendJs)
}

tasks.register<Delete>("clean") {
    delete(buildDir)
}

