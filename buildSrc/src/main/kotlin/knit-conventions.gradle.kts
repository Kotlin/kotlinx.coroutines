plugins {
    id("kotlinx-knit")
}

knit {
    siteRoot = "https://kotlinlang.org/api/kotlinx.coroutines"
    moduleRoots = listOf(".", "integration", "reactive", "ui")
    moduleDocs = "build/dokka-module/html/module"
    dokkaMultiModuleRoot = "build/dokka/html/"
}

tasks.named("knitPrepare") {
    dependsOn("dokkaGenerate")
}
