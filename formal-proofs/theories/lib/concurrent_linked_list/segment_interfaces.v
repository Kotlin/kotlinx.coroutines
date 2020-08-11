From iris.heap_lang Require Export notation.

Record linkedListNodeInterface :=
  LinkedListNodeInterface {
      getPrevLoc: val;
      getNextLoc: val;
    }.

Record segmentInterface :=
  SegmentInterface {
      base: linkedListNodeInterface;
      newSegment: val;
      getId: val;
      maxSlots: nat;
      pointerShift: nat;
      getCleanedAndPointersLoc: val;
    }.
