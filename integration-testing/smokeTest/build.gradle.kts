import org.jetbrains.kotlin.gradle.ExperimentalWasmDsl
import org.jetbrains.kotlin.gradle.dsl.HasConfigurableKotlinCompilerOptions
import org.jetbrains.kotlin.gradle.dsl.JvmTarget
import org.jetbrains.kotlin.gradle.dsl.KotlinJvmCompilerOptions
import org.jetbrains.kotlin.gradle.targets.js.nodejs.NodeJsRootExtension

plugins {
    id("org.jetbrains.kotlin.multiplatform")
}

repositories {
    mavenCentral()
    maven("https://maven.pkg.jetbrains.space/kotlin/p/kotlin/dev")
    maven("https://redirector.kotlinlang.org/maven/dev")
    // Coroutines from the outer project are published by previous CI builds step
    mavenLocal()
}

kotlin {
    jvm()
    js(IR) {
        nodejs()
    }
    @OptIn(ExperimentalWasmDsl::class)
    wasmJs {
        nodejs()
    }

    macosArm64()
    macosX64()
    linuxArm64()
    linuxX64()
    mingwX64()

    val coroutinesVersion = property("coroutines_version")

    sourceSets {
        commonMain {
            dependencies {
                implementation(kotlin("stdlib-common"))
                implementation("org.jetbrains.kotlinx:kotlinx-coroutines-core:$coroutinesVersion")
            }
        }
        commonTest {
            dependencies {
                implementation(kotlin("test-common"))
                implementation(kotlin("test-annotations-common"))
                implementation("org.jetbrains.kotlinx:kotlinx-coroutines-test:$coroutinesVersion")
            }
        }
        jsTest {
            dependencies {
                implementation(kotlin("test-js"))
            }
        }
        wasmJsTest {
            dependencies {
                implementation(kotlin("test-wasm-js"))
            }
        }
        wasmWasiTest {
            dependencies {
                implementation(kotlin("test-wasm-wasi"))
            }
        }
        jvmTest {
            dependencies {
                implementation(kotlin("test"))
                implementation(kotlin("test-junit"))
            }
        }
    }

    targets.all {
        val kotlinCompilerTaskName = compilations.getByName("main").compileKotlinTaskName
        @Suppress("UNCHECKED_CAST")
        val kotlinCompilerTask = tasks.getByName(kotlinCompilerTaskName) as? HasConfigurableKotlinCompilerOptions<KotlinJvmCompilerOptions>
        kotlinCompilerTask?.compilerOptions {
            jvmTarget.set(JvmTarget.JVM_1_8)
        }
    }
}
