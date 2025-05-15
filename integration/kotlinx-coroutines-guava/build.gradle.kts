val guavaVersion = "31.0.1-jre"

dependencies {
    api("com.google.guava:guava:$guavaVersion")
}

java {
    targetCompatibility = JavaVersion.VERSION_1_8
    sourceCompatibility = JavaVersion.VERSION_1_8
}

externalDocumentationLink(
    url = "https://google.github.io/guava/releases/$guavaVersion/api/docs/"
)
