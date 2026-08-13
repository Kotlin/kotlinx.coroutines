plugins {
    id("org.openjfx.javafxplugin")
}

configurations {
    register("javafx")
    named("compileOnly") {
        extendsFrom(configurations["javafx"])
    }
    named("testImplementation") {
        extendsFrom(configurations["javafx"])
    }
}

javafx {
    version = version("javafx")
    modules = listOf("javafx.controls")
    configuration = "javafx"
}
