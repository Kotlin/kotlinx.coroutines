plugins {
    id("ru.vyarus.animalsniffer")
}

project.plugins.withType(JavaPlugin::class.java) {
    val signature: Configuration by configurations
    dependencies {
        signature("net.sf.androidscents.signature:android-api-level-14:4.0_r4@signature")
        signature("org.codehaus.mojo.signature:java17:1.0@signature")
    }
}
