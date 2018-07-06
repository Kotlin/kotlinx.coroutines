/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental

import java.security.Permission

class TestSecurityManager : SecurityManager() {
    override fun checkPropertyAccess(key: String?) {
        if (key?.startsWith("kotlinx.") == true)
            throw SecurityException("'$key' property is not allowed")
    }

    override fun checkPermission(perm: Permission?) {
        /* allow everything else */
    }
}