From iris.heap_lang Require Export proofmode notation lang.
From SegmentQueue.lib.util Require Export addAndGet addConditionally.

Definition CLOSED: val := #0.

Record linkedListNodeInterface :=
  LinkedListNodeInterface {
      getPrevLoc: val;
      getNextLoc: val;
    }.

Section LinkedListNode.

Variable impl: linkedListNodeInterface.

Definition trySetNext: val :=
  λ: "this" "value", CAS (getNextLoc impl "this") NONE (SOME "value").

Definition getPrev: val :=
  λ: "this", !(getPrevLoc impl "this").

Definition getNextOrIfClosed: val :=
  (λ: "this" "onClosed", match: !(getNextLoc impl "this") with
                           InjR "v" => if: "v" = #() then #()
                                       else if: "v" = CLOSED then "onClosed" #()
                                            else "undefined"
                         | InjL "v" => NONEV
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

Record segmentInterface :=
  SegmentInterface {
      base: linkedListNodeInterface;
      newSegment: val;
      getId: val;
      maxSlots: nat;
      pointerShift: nat;
      getCleanedAndPointersLoc: val;
    }.

Section Segment.

Variable impl: segmentInterface.

Definition getIsRemoved: val :=
  λ: "this", (!(getCleanedAndPointersLoc impl "this") = #(maxSlots impl)) &&
             ~ isTail (base impl) "this".

Definition leftmostAliveNodeInternal: val :=
  λ: "this", (rec: "loop" "cur" :=
                if: "cur" ≠ NONEV && getIsRemoved "cur"
                then "loop" (getPrev (base impl) "cur")
                else "cur") (getPrev (base impl) "this").

Definition rightmostAliveNodeInternal: val :=
  λ: "this", if: isTail (base impl) "this" then "undefined"
             else (rec: "loop" "cur" :=
                     if: getIsRemoved "cur"
                     then "loop" (getNext (base impl) "cur")
                     else "cur")
                    (getNext (base impl) "this").

Definition remove: val :=
  λ: "this", if: getIsRemoved "this" && ~ isTail (base impl) "this"
             then (rec: "loop" <> :=
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
                          | SOME "prev'" => if: getIsRemoved "prev"
                                            then "loop" #()
                                            else #()
                          end) #()
             else "undefined".

Definition tryIncPointers: val :=
  λ: "this", addConditionally (!(getCleanedAndPointersLoc impl "this"))
                              #(1 ≪ pointerShift impl)
                              (λ: "it", "it" ≠ #(maxSlots impl) &&
                                        ~ isTail (base impl) "this").

Definition decPointers: val :=
  λ: "this", (addAndGet (!(getCleanedAndPointersLoc impl "this"))
                        #(-(1 ≪ pointerShift impl)) = #(maxSlots impl)) &&
             ~ isTail (base impl) "this".

Definition findSegmentInternal : val :=
  λ: "this" "id",
  (rec: "loop" "cur" :=
     if: "id" ≤ getId impl "cur" && ~ getIsRemoved "cur" then SOME "cur"
     else match: !(getNextLoc (base impl) "cur") with
            InjL "v" => if: "v" = CLOSED
                        then NONEV
                        else if: "v" = #() then
                               let: "newTail" := newSegment
                                                   impl
                                                   (#1%nat + getId impl "cur")
                                                   (SOME "cur")
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
  rec: "loop" <> := let: "cur" := ! "ptr" in
                    if: getId impl "to" ≤ getId impl "cur"
                    then #true
                    else if: tryIncPointers "to"
                         then if: CAS "ptr" "cur" "to"
                              then #()
                              else (if: decPointers "to"
                                    then remove "to"
                                    else #()) ;;
                                   "loop" #()
                         else #false.

Definition findSegmentAndMoveForward : val :=
  λ: "ptr" "id" "startFrom",
  (rec: "loop" <> := match: findSegmentInternal "startFrom" "id" with
                       NONE => NONE
                     | SOME "v" => if: moveForward "ptr" "v"
                                   then SOME "v"
                                   else "loop" #()
                     end) #().

End Segment.
