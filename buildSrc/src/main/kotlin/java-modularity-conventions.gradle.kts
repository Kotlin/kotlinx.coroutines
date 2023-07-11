/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

// Currently the compilation of the module-info fails for
// kotlinx-coroutines-play-services because it depends on Android JAR's
// which do not have an explicit module-info descriptor.
// Because the JAR's are all named `classes.jar`,
// the automatic module name also becomes `classes`.
// This conflicts since there are multiple JAR's with identical names.
val invalidModules = listOf("kotlinx-coroutines-play-services")

configure(subprojects.filter {
    !unpublished.contains(it.name) && !invalidModules.contains(it.name) && it.extensions.findByName("kotlin") != null
}) {
    Java9Modularity.configure(project)
}
