From iris.heap_lang Require Export proofmode notation lang.
Require Export SegmentQueue.lib.concurrent_linked_list.segment_interfaces.

Section SQSegment_impl.

Variable maxSlots: positive.
Variable pointerShift: positive.

Definition getDataLoc: val :=
  λ: "this", Snd (!"this").

Definition SQSegmentListNode :=
  {| segment_interfaces.getPrevLoc := λ: "this", Snd (Fst (Fst (!"this")));
     segment_interfaces.getNextLoc := λ: "this", Snd (Fst (!"this"));
  |}.

Definition SQSegment :=
  {| segment_interfaces.base := SQSegmentListNode;
     segment_interfaces.newSegment :=
       λ: "id" "prev" "pointers",
       ref ("id", ref ("pointers" ≪ #(Zpos pointerShift)), ref "prev", ref NONE,
            AllocN #(Zpos maxSlots) NONE);
     segment_interfaces.getId :=
       λ: "this", Fst (Fst (Fst (Fst (!"this"))));
     segment_interfaces.maxSlots := Pos.to_nat maxSlots;
     segment_interfaces.pointerShift := Pos.to_nat pointerShift;
     segment_interfaces.getCleanedAndPointersLoc :=
       λ: "this", Snd (Fst (Fst (Fst (!"this"))));
  |}.

End SQSegment_impl.
