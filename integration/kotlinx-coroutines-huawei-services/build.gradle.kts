/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

val tasksVersion = "1.5.0.300"

val artifactType = Attribute.of("artifactType", String::class.java)
val unpackedAar = Attribute.of("unpackedAar", Boolean::class.javaObjectType)

configurations.configureEach {
    afterEvaluate {
        if (isCanBeResolved) {
            attributes.attribute(unpackedAar, true) // request all AARs to be unpacked
        }
    }
}

repositories {
    maven { url = uri("https://developer.huawei.com/repo/") }
}

dependencies {
    attributesSchema {
        attribute(unpackedAar)
    }

    artifactTypes {
        create("aar") {
            attributes.attribute(unpackedAar, false)
        }
    }

    registerTransform(UnpackAar::class.java) {
        from.attribute(unpackedAar, false).attribute(artifactType, "aar")
        to.attribute(unpackedAar, true).attribute(artifactType, "jar")
    }

    api("com.huawei.hmf:tasks:$tasksVersion") {
        exclude(group="com.android.support")
    }
}

externalDocumentationLink(
    url = "https://developer.huawei.com/consumer/en/hms"
)
