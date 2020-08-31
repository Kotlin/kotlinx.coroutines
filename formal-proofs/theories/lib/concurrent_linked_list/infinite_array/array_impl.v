From iris.heap_lang Require Export proofmode notation lang.
Require Import SegmentQueue.lib.concurrent_linked_list.list_interfaces.
From SegmentQueue.lib.concurrent_linked_list.infinite_array Require Import
     array_interfaces sqsegment_impl.

Section array_impl.

Variable (segment_size pointer_shift: positive).

Variable list_impl: listInterface.

Definition fromSome: val :=
  λ: "this", match: "this" with
               InjL "v" => "undefined"
             | InjR "v" => "v"
             end.

Definition getIdImpl := getId (SQSegment segment_size pointer_shift).

Definition InfiniteArray :=
  {| array_interfaces.cancelCell :=
       λ: "ptr", onSlotCleaned list_impl (Fst "ptr");
     array_interfaces.newInfiniteArray := newList list_impl;
     array_interfaces.findCell :=
       λ: "ptr" "id",
       let: "sid" := "id" `quot` #(Pos.to_nat segment_size) in
       let: "cid" := "id" `rem` #(Pos.to_nat segment_size) in
       let: "seg" := fromSome (findSegment list_impl "ptr" "sid") in
       if: getIdImpl "seg" = "sid"
       then ("seg", "cid")
       else ("seg", #0);
     array_interfaces.derefCellPointer :=
       λ: "ptr", let: "seg" := Fst "ptr" in
                 let: "ix" := Snd "ptr" in
                 getDataLoc "seg" +ₗ "ix";
     array_interfaces.cutoffMoveForward :=
       λ: "cutoff" "ptr", moveForward list_impl "cutoff" (Fst "ptr");
     array_interfaces.cutoffGetPointer := λ: "cutoff", !"cutoff";
     array_interfaces.cellPointerId :=
       λ: "ptr", let: "seg" := Fst "ptr" in
                 let: "ix" := Snd "ptr" in
                 getIdImpl "seg"
                 * #(Pos.to_nat segment_size) + "ix";
     array_interfaces.cellPointerCleanPrev :=
       λ: "ptr", cleanPrev list_impl (Fst "ptr");
  |}.

End array_impl.
