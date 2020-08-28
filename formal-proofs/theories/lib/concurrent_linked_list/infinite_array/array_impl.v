From iris.heap_lang Require Export proofmode notation lang.
Require Import SegmentQueue.lib.concurrent_linked_list.list_interfaces.
Require Import SegmentQueue.lib.concurrent_linked_list.infinite_array.sqsegment_impl.

Section array_impl.

Variable (segment_size pointer_shift: positive).

Variable list_impl: listInterface.

Definition newInfiniteArray: val :=
  newList list_impl.

Definition cancelCell: val :=
  λ: "ptr", onSlotCleaned list_impl (Fst "ptr").

Definition fromSome: val :=
  λ: "this", match: "this" with
               InjL "v" => "undefined"
             | InjR "v" => "v"
             end.

Definition findCell: val :=
  λ: "ptr" "id",
  let: "sid" := "id" `quot` #(Pos.to_nat segment_size) in
  let: "cid" := "id" `rem` #(Pos.to_nat segment_size) in
  let: "seg" := fromSome (findSegment list_impl "ptr" "sid") in
  if: getId "seg" = "sid"
  then ("seg", "cid")
  else ("seg", #0).

Definition derefCellPointer: val :=
  λ: "ptr", let: "seg" := Fst "ptr" in
            let: "ix" := Snd "ptr" in
            getDataLoc "seg" +ₗ "ix".

Definition cellPointerId: val :=
  λ: "ptr", let: "seg" := Fst "ptr" in
            let: "ix" := Snd "ptr" in
            getId "seg" * #(Pos.to_nat segment_size) + "ix".

Definition cellPointerCleanPrev: val :=
  λ: "ptr", cleanPrev list_impl (Fst "ptr").

Definition cutoffMoveForward: val :=
  λ: "cutoff" "ptr", moveForward list_impl "cutoff" (Fst "ptr").

Definition cutoffGetPointer: val :=
  λ: "cutoff", !"cutoff".

End array_impl.
