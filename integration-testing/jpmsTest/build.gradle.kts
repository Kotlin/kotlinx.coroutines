plugins {
    kotlin("jvm")
}

val coroutinesVersion = providers.gradleProperty("coroutines_version").get()

java {
    modularity.inferModulePath.set(true)
}

kotlin {
    jvmToolchain(17)

    val test = target.compilations.getByName("test")
    target.compilations.create("debugDynamicAgentJpmsTest") {
        associateWith(test)


        defaultSourceSet.dependencies {
            implementation("org.jetbrains.kotlinx:kotlinx-coroutines-core:$coroutinesVersion")
            implementation("org.jetbrains.kotlinx:kotlinx-coroutines-debug:$coroutinesVersion")
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

