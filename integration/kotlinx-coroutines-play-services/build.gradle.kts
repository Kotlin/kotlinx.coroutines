/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

ext.tasks_version = '16.0.1'

def artifactType = Attribute.of("artifactType", String)
def unpackedAar = Attribute.of("unpackedAar", Boolean)

configurations.all {
    afterEvaluate {
        if (canBeResolved) {
            attributes.attribute(unpackedAar, true) // request all AARs to be unpacked
        }
    }
}

dependencies {
    attributesSchema {
        attribute(unpackedAar)
    }

    artifactTypes {
        aar {
            attributes.attribute(unpackedAar, false)
        }
    }

    registerTransform(UnpackAar) {
        from.attribute(unpackedAar, false).attribute(artifactType, "aar")
        to.attribute(unpackedAar, true).attribute(artifactType, "jar")
    }

    api("com.google.android.gms:play-services-tasks:$tasks_version") {
        exclude group: 'com.android.support'
    }
}

tasks.withType(dokka.getClass()) {
    externalDocumentationLink {
        url = new URL("https://developers.google.com/android/reference/")
        // This is workaround for missing package list in Google API
        packageListUrl = projectDir.toPath().resolve("package.list").toUri().toURL()
    }
}
