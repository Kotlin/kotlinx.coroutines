@file:Suppress("PropertyName")
plugins {
    kotlin("jvm")
}

val coroutines_version: String by project

repositories {
    if (project.properties["build_snapshot_train"]?.toString()?.toBoolean() == true) {
        maven("https://maven.pkg.jetbrains.space/kotlin/p/kotlin/dev")
        maven("https://redirector.kotlinlang.org/maven/dev")
    }
    mavenLocal()
    mavenCentral()
}

java {
    modularity.inferModulePath.set(true)
}

kotlin {
    jvmToolchain(17)

    val test = target.compilations.getByName("test")
    target.compilations.create("debugDynamicAgentJpmsTest") {
        associateWith(test)


        defaultSourceSet.dependencies {
            implementation("org.jetbrains.kotlinx:kotlinx-coroutines-core:$coroutines_version")
            implementation("org.jetbrains.kotlinx:kotlinx-coroutines-debug:$coroutines_version")
        }

        tasks.register<Test>("debugDynamicAgentJpmsTest") {
            testClassesDirs = output.classesDirs
            classpath = javaSourceSet.runtimeClasspath
        }
    }
}

tasks.named("check") {
    dependsOn(tasks.withType<Test>())
}

dependencies {
    testImplementation(kotlin("test-junit"))
}

