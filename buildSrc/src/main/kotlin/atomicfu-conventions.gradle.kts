plugins {
    id("org.jetbrains.kotlinx.atomicfu")
}

// Workaround for KT-71203. Can be removed after https://github.com/Kotlin/kotlinx-atomicfu/issues/431
atomicfu {
    transformJs = false
}
