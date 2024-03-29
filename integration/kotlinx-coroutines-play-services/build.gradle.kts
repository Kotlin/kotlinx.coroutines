val tasksVersion = "16.0.1"

project.configureAar()

dependencies {
    configureAarUnpacking()
    api("com.google.android.gms:play-services-tasks:$tasksVersion") {
        exclude(group="com.android.support")
    }

    // Required by robolectric
    testImplementation("androidx.test:core:1.2.0")
    testImplementation("androidx.test:monitor:1.2.0")
}

externalDocumentationLink(
    url = "https://developers.google.com/android/reference/"
)
