dependencies {
    api(project(":kotlinx-coroutines-reactive"))
    testImplementation("org.reactivestreams:reactive-streams-tck:${version("reactive_streams")}")
    api("io.reactivex.rxjava3:rxjava:${version("rxjava3")}")
}

externalDocumentationLink("http://reactivex.io/RxJava/3.x/javadoc/")

val testNG = tasks.register<Test>("testNG") {
    useTestNG()
    reports.html.outputLocation = file("${layout.buildDirectory.get()}/reports/testng")
    include("**/*ReactiveStreamTckTest.*")
    // Skip testNG when tests are filtered with --tests, otherwise it simply fails
    onlyIf {
        filter.includePatterns.isEmpty()
    }
    doFirst {
        // Classic gradle, nothing works without doFirst
        println("TestNG tests: ($includes)")
    }
}

val test = tasks.getByName<Test>("test") {
    dependsOn(testNG)
    reports.html.outputLocation = file("${layout.buildDirectory.get()}/reports/junit")
}
