//package kotlinx.coroutines.internal
//
//import kotlinx.atomicfu.*
//import kotlin.test.*
//
//class SegmentListTest {
//    @Test
//    fun testRemoveTail() {
//        val initialSegment = TestSegment(0, null, 2)
//        val head = AtomicRefHolder(initialSegment)
//        val tail = AtomicRefHolder(initialSegment)
//        val s1 = tail.ref.findSegmentAndMoveForward(1, tail.ref.value, ::createTestSegment).segment
//        assertFalse(s1.removed)
//        tail.ref.value.onSlotCleaned()
//        assertFalse(s1.removed)
//        head.ref.findSegmentAndMoveForward(2, head.ref.value, ::createTestSegment)
//        assertFalse(s1.removed)
//        tail.ref.findSegmentAndMoveForward(2, head.ref.value, ::createTestSegment)
//        assertTrue(s1.removed)
//    }
//
//    @Test
//    fun testClose() {
//        val initialSegment = TestSegment(0, null, 2)
//        val head = AtomicRefHolder(initialSegment)
//        val tail = AtomicRefHolder(initialSegment)
//        tail.ref.findSegmentAndMoveForward(1, tail.ref.value, ::createTestSegment)
//        assertEquals(tail.ref.value, tail.ref.value.close())
//        assertTrue(head.ref.findSegmentAndMoveForward(2, head.ref.value, ::createTestSegment).isClosed)
//    }
//}
//
//private class AtomicRefHolder<T>(initialValue: T) {
//    val ref = atomic(initialValue)
//}
//
//private class TestSegment(id: Long, prev: TestSegment?, pointers: Int) : Segment<TestSegment>(id, prev, pointers) {
//    override val maxSlots: Int get() = 1
//}
//private fun createTestSegment(id: Long, prev: TestSegment?) = TestSegment(id, prev, 0)
