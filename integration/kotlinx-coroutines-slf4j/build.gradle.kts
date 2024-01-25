dependencies {
    implementation("org.slf4j:slf4j-api:1.7.32")
    testImplementation("io.github.microutils:kotlin-logging:2.1.0")
    testRuntimeOnly("ch.qos.logback:logback-classic:1.2.7")
    testRuntimeOnly("ch.qos.logback:logback-core:1.2.7")
}

externalDocumentationLink(
    url = "https://www.slf4j.org/apidocs/"
)
