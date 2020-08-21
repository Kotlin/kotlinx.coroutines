From iris.heap_lang Require Export proofmode notation lang.
From SegmentQueue.lib.util Require Export addAndGet addConditionally.
From SegmentQueue.lib.concurrent_linked_list
     Require Export segment_interfaces list_interfaces.

Definition CLOSED: val := #0.

Section LinkedListNode.

Variable impl: linkedListNodeInterface.

Definition trySetNext: val :=
  λ: "this" "value", CAS (getNextLoc impl "this") NONE (SOME "value").

Definition getPrev: val :=
  λ: "this", !(getPrevLoc impl "this").

Definition getNextOrIfClosed: val :=
  (λ: "this" "onClosed", match: !(getNextLoc impl "this") with
                           InjR "v" => InjR "v"
                         | InjL "v" => if: "v" = CLOSED
                                       then "onClosed" #()
                                       else if: "v" = #()
                                            then NONEV
                                            else "undefined"
                         end)%V.

Definition getNext: val :=
  λ: "this", getNextOrIfClosed "this" (λ: <>, NONEV).

Definition isTail: val :=
  λ: "this", getNext "this" = NONEV.

Definition cleanPrev: val :=
  λ: "this", getPrevLoc impl "this" <- NONEV.

Definition markAsClosed: val :=
  λ: "this", CAS (getNextLoc impl "this") NONEV CLOSED.

Definition closeList: val :=
  rec: "close" "cur" :=
    match: !(getNextLoc impl "cur") with
      InjL "v" => if: "v" = CLOSED then "cur"
                  else if: "v" = #()
                       then if: markAsClosed "cur"
                            then "cur"
                            else "close" "cur"
                       else "undefined"
    | InjR "v" => "close" "v"
    end.

End LinkedListNode.

Section Segment.

Variable impl: segmentInterface.

Definition getIsRemoved: val :=
  λ: "this", !(getCleanedAndPointersLoc impl "this") = #(maxSlots impl).

Definition leftmostAliveNodeInternal: val :=
  λ: "this", (rec: "loop" "cur" :=
                match: "cur" with
                  NONE => "cur"
                | SOME "v" => if: getIsRemoved "v"
                              then "loop" (getPrev (base impl) "v")
                              else "cur"
                end)%V (getPrev (base impl) "this").

Definition fromSome: val :=
  λ: "this", match: "this" with
               InjL "v" => "undefined"
             | InjR "v" => "v"
             end.

Definition rightmostAliveNodeInternal: val :=
  λ: "this", if: isTail (base impl) "this" then "undefined" else
               (rec: "loop" "cur" :=
                  if: getIsRemoved "cur" && ~ isTail (base impl) "cur"
                  then "loop" (fromSome (getNext (base impl) "cur"))
                  else "cur")%V (fromSome (getNext (base impl) "this")).

Definition remove: val :=
  λ: "this", if: ~ getIsRemoved "this" then "undefined" else
               if: isTail (base impl) "this" then #() else
                 (rec: "loop" <> :=
                    let: "prev" := leftmostAliveNodeInternal "this" in
                    let: "next" := rightmostAliveNodeInternal "this" in
                    getPrevLoc (base impl) "next" <- "prev" ;;
                    (match: "prev" with
                       NONE => #()
                     | SOME "prev'" =>
                       getNextLoc (base impl) "prev'" <- SOME "next"
                     end) ;;
                    if: getIsRemoved "next"
                    then "loop" #()
                    else match: "prev" with
                           NONE => #()
                         | SOME "prev'" => if: getIsRemoved "prev'"
                                           then "loop" #()
                                           else #()
                         end) #().

Definition tryIncPointersHelper: val :=
  λ: "ptr", addConditionally "ptr"
                              #(1 ≪ pointerShift impl)
                              (λ: "it", "it" ≠ #(maxSlots impl)).

Definition tryIncPointers: val :=
  λ: "this", tryIncPointersHelper (getCleanedAndPointersLoc impl "this").

Definition decPointers: val :=
  λ: "this", addAndGet (getCleanedAndPointersLoc impl "this")
                       #(-(1 ≪ pointerShift impl)) = #(maxSlots impl).

Definition findSegmentInternal : val :=
  λ: "this" "id",
  (rec: "loop" "cur" :=
     if: ("id" ≤ getId impl "cur") && ~ getIsRemoved "cur" then SOME "cur"
     else match: !(getNextLoc (base impl) "cur") with
            InjL "v" => if: "v" = CLOSED
                        then NONEV
                        else if: "v" = #() then
                               let: "newTail" := newSegment
                                                   impl
                                                   (#1%nat + getId impl "cur")
                                                   (SOME "cur")
                                                   #0%nat
                               in if: trySetNext (base impl) "cur" "newTail"
                                  then (if: getIsRemoved "cur"
                                        then remove "cur"
                                        else #()) ;;
                                       "loop" "newTail"
                                  else "loop" "cur"
                             else "undefined"
          | InjR "v" => "loop" "v"
          end) "this".

Definition moveForward : val :=
  λ: "ptr" "to",
  (rec: "loop" <> := let: "cur" := ! "ptr" in
                     if: getId impl "to" ≤ getId impl "cur"
                     then #true
                     else if: tryIncPointers "to"
                          then if: CAS "ptr" "cur" "to"
                               then (if: decPointers "cur"
                                     then remove "cur"
                                     else #()) ;;
                                    #true
                               else (if: decPointers "to"
                                     then remove "to"
                                     else #()) ;;
                                    "loop" #()
                          else #false) #().

Definition findSegmentAndMoveForward : val :=
  λ: "ptr" "id" "startFrom",
  (rec: "loop" <> := match: findSegmentInternal "startFrom" "id" with
                       NONE => NONE
                     | SOME "v" => if: moveForward "ptr" "v"
                                   then SOME "v"
                                   else "loop" #()
                     end) #().

Definition onSlotCleaned : val :=
  λ: "ptr", if: FAA (getCleanedAndPointersLoc impl "ptr") #1 + #1 =
                #(maxSlots impl)
            then remove "ptr"
            else #().

Definition newList : val :=
  λ: "k", AllocN "k" (newSegment impl #0%nat NONEV "k").

Canonical Structure list_impl: listInterface :=
  {| list_interfaces.newList := newList;
     list_interfaces.cleanPrev := cleanPrev (base impl);
     list_interfaces.findSegment := findSegmentInternal;
     list_interfaces.moveForward := moveForward;
     list_interfaces.onSlotCleaned := onSlotCleaned;
  |}.

End Segment.
