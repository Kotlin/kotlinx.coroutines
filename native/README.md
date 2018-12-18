# Coroutines core for Kotlin/Native

This directory contains modules that provide core coroutines support on Kotlin/Native.

## Using in your projects

Use [`org.jetbrains.kotlinx:kotlinx-coroutines-core-native:<version>`](kotlinx-coroutines-core-native/README.md)
module in your Gradle/Maven dependencies. 
Only single-threaded code (JS-style) is currently supported. 

Kotlin/Native libraries would only work under Gradle version 4.7 (**exactly**) 
and you should use `kotlin-platform-native` plugin.

First of all, you'll need to enable Gradle metadata in your
`settings.gradle` file:

```groovy
enableFeaturePreview('GRADLE_METADATA')
```

Then, you'll need to apply the corresponding plugin and add appropriate dependencies in your
`build.gradle` file:

```groovy
buildscript {
    repositories {
        jcenter()
        maven { url 'https://plugins.gradle.org/m2/' }
        maven { url 'https://dl.bintray.com/jetbrains/kotlin-native-dependencies' }
    }

    dependencies {
        classpath "org.jetbrains.kotlin:kotlin-native-gradle-plugin:$kotlin_native_version"
    }

}

apply plugin: 'kotlin-platform-native'

repositories {
    jcenter()
}

dependencies {
    implementation 'org.jetbrains.kotlinx:kotlinx-coroutines-core-native:1.1.0-alpha'
}

sourceSets {
    main {
        component {
            targets = ["ios_arm64", "ios_arm32", "ios_x64", "macos_x64", "linux_x64", "mingw_x64"] 
            outputKinds = [EXECUTABLE]
        }
    }
}
```

Since Kotlin/Native does not generally provide binary compatibility between versions, 
you should use the same version of Kotlin/Native compiler as was used to build `kotlinx.coroutines`. 
Add an appropriate `kotlin_native_version` to your `gradle.properties` file. 
See [gradle.properties](../gradle.properties). 

