import org.gradle.kotlin.dsl.configure
import org.gradle.kotlin.dsl.withType
import org.jetbrains.kotlin.gradle.dsl.KotlinJvmExtension
import org.jetbrains.kotlin.gradle.dsl.KotlinMultiplatformExtension
import org.jetbrains.kotlin.gradle.targets.jvm.KotlinJvmTarget

// This convention plugin restores behavior  that was before changes in https://youtrack.jetbrains.com/issue/KT-69701

plugins.withId("org.jetbrains.kotlin.jvm") {
    extensions.configure<KotlinJvmExtension>() {
        compilerOptions.moduleName.value(project.name)
    }
}

plugins.withId("org.jetbrains.multiplatform") {
    extensions.configure<KotlinMultiplatformExtension>() {
        targets.withType<KotlinJvmTarget>() {
            compilerOptions.moduleName.value(project.name)
        }
    }
}
