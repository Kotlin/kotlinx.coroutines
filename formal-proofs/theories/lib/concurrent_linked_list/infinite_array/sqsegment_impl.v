From iris.heap_lang Require Export proofmode notation lang.
Require Import SegmentQueue.lib.concurrent_linked_list.segment_interfaces.

Section SQSegment_impl.

Variable maxSlots: positive.
Variable pointerShift: positive.

Definition newSegment: val :=
  λ: "id" "prev" "pointers",
  ref ("id", ref ("pointers" ≪ #(Zpos pointerShift)), ref "prev", ref NONE,
       AllocN #(Zpos maxSlots) NONE).

Definition getPrevLoc: val :=
  λ: "this", Snd (Fst (Fst (!"this"))).

Definition getNextLoc: val :=
  λ: "this", Snd (Fst (!"this")).

Definition getCleanedAndPointersLoc: val :=
  λ: "this", Snd (Fst (Fst (Fst (!"this")))).

Definition getId: val :=
  λ: "this", Fst (Fst (Fst (Fst (!"this")))).

Definition getDataLoc: val :=
  λ: "this", Snd (!"this").

Definition SQSegmentListNode :=
  {| segment_interfaces.getPrevLoc := getPrevLoc;
     segment_interfaces.getNextLoc := getNextLoc;
  |}.

Definition SQSegment :=
  {| segment_interfaces.base := SQSegmentListNode;
     segment_interfaces.newSegment := newSegment;
     segment_interfaces.getId := getId;
     segment_interfaces.maxSlots := Pos.to_nat maxSlots;
     segment_interfaces.pointerShift := Pos.to_nat pointerShift;
     segment_interfaces.getCleanedAndPointersLoc := getCleanedAndPointersLoc
  |}.

End SQSegment_impl.
