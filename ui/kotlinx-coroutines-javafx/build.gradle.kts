/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

buildscript {
    dependencies {
        // this line can be removed when https://github.com/openjfx/javafx-gradle-plugin/pull/135 is released
        classpath("org.javamodularity:moduleplugin:1.8.12")
    }
}

plugins {
    id("org.openjfx.javafxplugin") version "0.0.13"
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
