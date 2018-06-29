/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package cases.nestedClasses

public object PublicObject {

    public object ObjPublic
    internal object ObjInternal
    private object ObjPrivate

    public class NestedPublic
    internal class NestedInternal
    private class NestedPrivate

    public interface NestedPublicInterface
    internal interface NestedInternalInterface
    private interface NestedPrivateInterface
}

