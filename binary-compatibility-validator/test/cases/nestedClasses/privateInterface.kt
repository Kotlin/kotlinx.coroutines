/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package cases.nestedClasses

private interface PrivateInterface {
    public object ObjPublic
    private object ObjPrivate

    public class NestedPublic
    private class NestedPrivate

    public interface NestedPublicInterface
    private interface NestedPrivateInterface

}

