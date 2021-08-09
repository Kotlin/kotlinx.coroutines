/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels.koval_europar

import sun.misc.Unsafe

public object UtilUnsafe {
    public val unsafe: Unsafe
        get() {
            if (UtilUnsafe::class.java.classLoader == null)
                return Unsafe.getUnsafe()
            try {
                val fld = Unsafe::class.java.getDeclaredField("theUnsafe")
                fld.isAccessible = true
                return fld.get(UtilUnsafe::class.java) as Unsafe
            } catch (e: Exception) {
                throw RuntimeException("Could not obtain access to sun.misc.Unsafe", e)
            }
        }
}