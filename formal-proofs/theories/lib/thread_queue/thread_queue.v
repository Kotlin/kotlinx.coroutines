From SegmentQueue.util Require Import
  everything local_updates big_opL cmra count_matching find_index.

Require Import SegmentQueue.lib.util.getAndSet.
Require Import SegmentQueue.lib.util.future.
From iris.heap_lang Require Import notation.
From SegmentQueue.lib.concurrent_linked_list.infinite_array
     Require Import array_spec iterator.iterator_impl.

Notation RESUMEDV := (InjLV #0).
Notation CANCELLEDV := (InjLV #1).
Notation BROKENV := (InjLV #2).
Notation TAKENV := (InjLV #3).
Notation REFUSEDV := (InjLV #4).

Section impl.

Variable array_interface: infiniteArrayInterface.

Definition fromSome: val :=
  λ: "this", match: "this" with
               InjL "v" => "undefined"
             | InjR "v" => "v"
             end.

Definition suspend: val :=
  λ: "enqIterator",
  let: "future" := emptyFuture #() in
  let: "cellPtr" := Snd (iteratorStep array_interface "enqIterator") in
  let: "cell" := derefCellPointer array_interface "cellPtr" in
  let: "future'" := SOME ("future", "cellPtr") in
  if: CAS "cell" (InjLV #()) (InjL "future")
  then "future'"
  else let: "value" := !"cell" in
       if: ("value" ≠ BROKENV) && CAS "cell" "value" TAKENV
       then tryCompleteFuture "future" (fromSome "value") ;; SOME ("future", #())
       else NONEV.

Definition tryResume: val :=
  λ: "maxWait" "shouldAdjust" "mayBreakCells" "waitForResolution" "deqIterator"
     "returnRefusedValue" "value",
  match: iteratorStepOrIncreaseCounter
           array_interface "shouldAdjust" "deqIterator" with
      NONE => #1
    | SOME "cellPtr" =>
      cellPointerCleanPrev array_interface "cellPtr" ;;
      (rec: "modify_cell" <> :=
         let: "cell" := derefCellPointer array_interface "cellPtr" in
         let: "cellState" := !"cell" in
         if: "cellState" = NONEV then
           if: CAS "cell" NONEV (SOME "value") then
             if: "mayBreakCells" then
               if: (rec: "wait" "n" :=
                      ("n" ≠ #0) && ((!"cell" = TAKENV) || "wait" ("n" - #1)))
                     "maxWait"
                   || (~ CAS "cell" (SOME "value") BROKENV)
               then #0
               else #2
             else #0
           else "modify_cell" #()
         else if: "cellState" = CANCELLEDV then #1
         else if: "cellState" = REFUSEDV then "returnRefusedValue" "value" ;; #0
         else match: "cellState" with
                InjR "x" => "undefined"
              | InjL "th" => let: "success" := tryCompleteFuture "th" "value" in
                            if: "success" then
                              "cell" <- RESUMEDV ;; #0
                            else
                              if: "shouldAdjust"
                              then if: "waitForResolution" then "modify_cell" #()
                                   else if: CAS "cell" (InjL "th") (SOME "value")
                                        then #0
                                        else "modify_cell" #()
                              else #1
              end) #()
  end.

Definition resume: val :=
  λ: "maxWait" "skipCancelled" "mayBreakCells" "waitForResolution"
     "deqIterator" "returnRefusedValue" "value",
  (rec: "resume" <> :=
    let: "result" := tryResume "maxWait" "skipCancelled" "mayBreakCells"
                               "waitForResolution" "deqIterator"
                               "returnRefusedValue" "value" in
    if: "result" = #0 then #true
    else if: "result" = #1 then
           if: "skipCancelled" then "resume" #()
           else #false
    else if: "result" = #2 then #false
    else "undefined") #().

Definition cancellationHandler: val :=
  λ: "maxWait" "mayBreakCells" "waitForResolution" "deqIterator"
     "checkCancellation" "returnRefusedValue" "returnValue" "cellPtr",
    let: "cell" := derefCellPointer array_interface "cellPtr" in
    let: "cancellationAllowed" := "checkCancellation" #() in
    if: "cancellationAllowed" then
      let: "markResult" := getAndSet "cell" CANCELLEDV in
      cancelCell array_interface "cellPtr" ;;
      match: "markResult" with
        InjR "v" => if: resume "maxWait" #true "mayBreakCells"
                              "waitForResolution" "deqIterator"
                              "returnRefusedValue" "v"
                   then #()
                   else "returnValue" "v"
      | InjL "th" => #()
      end
    else
      match: getAndSet "cell" REFUSEDV with
        InjR "v" => "returnRefusedValue" "v"
      | InjL "th" => #()
      end.

Definition tryCancelThreadQueueFuture: val :=
  λ: "f", tryCancelFuture (Fst "f").

Definition awaitThreadQueueFuture: val :=
  λ: "f", awaitFuture (Fst "f").

Definition fillThreadQueueFuture: val := λ: "v", (completeFuture "v", #()).

Definition tryCancelThreadQueueFuture': val :=
  λ: "immediate" "maxWait" "mayBreakCells" "waitForResolution"
     "deqIterator" "checkCancellation" "returnRefusedValue" "returnValue" "f",
  if: tryCancelThreadQueueFuture "f"
  then let: "future" := Fst "f" in
       let: "cellPtr" := Snd "f" in
       (if: "immediate" then
          let: "cell" := derefCellPointer array_interface "cellPtr" in
          getAndSet "cell" CANCELLEDV ;; cancelCell array_interface "cellPtr"
        else
          cancellationHandler "maxWait" "mayBreakCells" "waitForResolution"
                              "deqIterator" "checkCancellation"
                              "returnRefusedValue" "returnValue" "cellPtr"
       ) ;; #true
  else #false.

Definition newThreadQueue: val :=
  λ: <>, let: "arr" := newInfiniteArray array_interface #2 in
        (newIterator ("arr" +ₗ #0) #0,
         newIterator ("arr" +ₗ #1) #0).

End impl.

From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import proofmode.
From iris.algebra Require Import auth numbers list gset excl csum.

Section proof.

(** State **)

Inductive cellRendezvousResolution :=
| cellRendezvousSucceeded
| cellBroken.

Inductive cancellationResult :=
| cellTookValue (v: base_lit)
| cellClosed.

Inductive cancellationResolution :=
| cancellationAllowed (result: option cancellationResult)
| cancellationPrevented.

Inductive futureTerminalState :=
| cellResumed (v: base_lit)
| cellImmediatelyCancelled
| cellCancelled (resolution: option cancellationResolution).

Inductive cellState :=
| cellPassedValue (v: base_lit) (resolution: option cellRendezvousResolution)
| cellInhabited (futureName: gname) (futureLoc: val)
                (resolution: option futureTerminalState).

(** Resource algebras **)

Notation cellInhabitantThreadR := (agreeR (prodO gnameO valO)).

Notation inhabitedCellStateR :=
  (optionR
     (csumR
        (* Future was resumed. *)
        (agreeR valO)
        (* Future was cancelled. *)
        (csumR
           (* Cell was immediately cancelled. *)
           (agreeR unitO)
           (* Cell ony attempts cancellation. *)
           (prodUR
              (* Permits to attempt the later stages of cancellatoin. *)
              natUR
              (optionUR
                 (csumR
                    (* cancellation was logically impossible. *)
                    (agreeR unitO)
                    (* cancellation was allowed. *)
                    (optionUR
                       (csumR
                          (* a value was passed to the cell nonetheless. *)
                          (agreeR valO)
                          (* cancellation completed successfully. *)
                          (agreeR unitO))))))))).

Notation cellStateR :=
  (csumR
     (* Cell was filled with a value. *)
     (prodR
        (agreeR valO)
        (prodUR
           (optionUR (exclR unitO))
           (optionUR
           (* true: value was taken. false: cell is broken. *)
              (agreeR boolO))))
     (* Cell was inhabited. *)
     (prodR
        (* Description of the stored future. *)
        cellInhabitantThreadR
        inhabitedCellStateR)).

Notation queueContentsUR :=
  (prodUR (listUR (optionUR cellStateR))
          (optionUR (exclR natO))).

Notation enqueueUR := natUR.
Notation dequeueUR := (prodUR natUR max_natUR).
Notation algebra := (authUR (prodUR (prodUR enqueueUR dequeueUR)
                                    queueContentsUR)).

Class threadQueueG Σ := ThreadQueueG { thread_queue_inG :> inG Σ algebra }.
Definition threadQueueΣ : gFunctors := #[GFunctor algebra].
Instance subG_threadQueueΣ {Σ} : subG threadQueueΣ Σ -> threadQueueG Σ.
Proof. solve_inG. Qed.

Context `{heapG Σ} `{iteratorG Σ} `{threadQueueG Σ} `{futureG Σ}.
Variable (N NFuture: namespace).
Let NTq := N .@ "tq".
Let NArr := N .@ "array".
Let NDeq := N .@ "deq".
Let NEnq := N .@ "enq".
Notation iProp := (iProp Σ).

Record thread_queue_parameters :=
  ThreadQueueParameters
    {
      is_immediate_cancellation: bool;
      enqueue_resource: iProp;
      dequeue_resource: iProp;
      cell_refusing_resource: iProp;
      passed_value_resource: base_lit -> iProp;
      cell_breaking_resource: iProp;
    }.

Variable parameters: thread_queue_parameters.
Let E := enqueue_resource parameters.
Let R := dequeue_resource parameters.
Let V := passed_value_resource parameters.
Let ERefuse := cell_refusing_resource parameters.
Let CB := cell_breaking_resource parameters.
Let immediateCancellation := is_immediate_cancellation parameters.

Global Instance base_lit_inhabited: Inhabited base_lit.
Proof. repeat econstructor. Qed.

Definition rendezvousResolution_ra r :=
  match r with
  | None => (Excl' (), None)
  | Some cellRendezvousSucceeded => (Excl' (), Some (to_agree true))
  | Some cellBroken => (None, Some (to_agree false))
  end.

Definition cancellationResult_ra r :=
  match r with
  | cellTookValue v => Cinl (to_agree #v)
  | cellClosed => Cinr (to_agree ())
  end.

Definition cancellationResolution_ra r :=
  match r with
  | cancellationAllowed r => Cinr (option_map cancellationResult_ra r)
  | cancellationPrevented => Cinl (to_agree ())
  end.

Definition cancellationResolution_ra' r :=
  match r with
  | None => (2, None)
  | Some d => (1, Some (cancellationResolution_ra d))
  end.

Definition futureTerminalState_ra r :=
  match r with
  | cellResumed v =>
    Cinl (to_agree #v)
  | cellImmediatelyCancelled => Cinr (Cinl (to_agree ()))
  | cellCancelled r => Cinr (Cinr (cancellationResolution_ra' r))
  end.

Definition cellState_ra (state: cellState): cellStateR :=
  match state with
  | cellPassedValue v d => Cinl (to_agree #v,
                                 rendezvousResolution_ra d)
  | cellInhabited γ f r => Cinr (to_agree (γ, f),
                                option_map futureTerminalState_ra r)
  end.

Definition rendezvous_state γtq i (r: option cellStateR) :=
  own γtq (◯ (ε, ({[ i := r ]}, ε))).

Global Instance rendezvous_state_persistent γtq i (r: cellStateR):
  CoreId r -> Persistent (rendezvous_state γtq i (Some r)).
Proof. apply _. Qed.

Definition inhabited_rendezvous_state γtq i (r: inhabitedCellStateR): iProp :=
  ∃ γf f, rendezvous_state γtq i (Some (Cinr (to_agree (γf, f), r))).

Global Instance inhabited_rendezvous_state_persistent γtq i r:
  CoreId r -> Persistent (inhabited_rendezvous_state γtq i r).
Proof. apply _. Qed.

Definition filled_rendezvous_state γtq i r: iProp :=
  ∃ v, rendezvous_state γtq i (Some (Cinl (to_agree v, r))).

Global Instance filled_rendezvous_state_persistent γtq i r:
  CoreId r -> Persistent (filled_rendezvous_state γtq i r).
Proof. apply _. Qed.

Definition cell_breaking_token (γtq: gname) (i: nat): iProp :=
  filled_rendezvous_state γtq i (Excl' (), ε).

Definition cancellation_registration_token (γtq: gname) (i: nat): iProp :=
  inhabited_rendezvous_state γtq i (Some (Cinr (Cinr (2, ε)))).

Definition cell_cancelling_token (γtq: gname) (i: nat): iProp :=
  inhabited_rendezvous_state γtq i (Some (Cinr (Cinr (1, ε)))).

Definition thread_queue_state γ (n: nat) :=
  own γ (◯ (ε, (ε, Excl' n))).

Global Instance thread_queue_state_timeless:
  Timeless (thread_queue_state γ n).
Proof. apply _. Qed.

Definition deq_front_at_least γtq (n: nat) :=
  own γtq (◯ (ε, (ε, MaxNat n), ε)).

Definition rendezvous_thread_locs_state (γtq γf: gname) (f: val) (i: nat): iProp :=
  rendezvous_state γtq i (Some (Cinr (to_agree (γf, f), None))).

Global Instance rendezvous_thread_locs_state_persistent γtq γt th i:
  Persistent (rendezvous_thread_locs_state γtq γt th i).
Proof. apply _. Qed.

Definition rendezvous_filled_value (γtq: gname) (v: val) (i: nat): iProp :=
  rendezvous_state γtq i (Some (Cinl (to_agree v, ε))).

Definition V' (v: val): iProp := ∃ (x: base_lit), ⌜v = #x⌝ ∧ V x ∗ R.

Definition rendezvous_thread_handle (γtq γt: gname) th (i: nat): iProp :=
  (is_future NFuture V' γt th ∗ rendezvous_thread_locs_state γtq γt th i)%I.

Global Instance rendezvous_thread_handle_persistent γtq γt th i:
  Persistent (rendezvous_thread_handle γtq γt th i).
Proof. apply _. Qed.

Definition rendezvous_initialized γtq i: iProp :=
  inhabited_rendezvous_state γtq i ε ∨ filled_rendezvous_state γtq i ε.

Definition suspension_permit γ := own γ (◯ (1%nat, ε, ε)).

Definition awakening_permit γ := own γ (◯ (ε, (1%nat, ε), ε)).

Variable array_interface: infiniteArrayInterface.
Variable array_spec: infiniteArraySpec _ array_interface.

Let cell_location γtq :=
  infinite_array_mapsto _ _ array_spec NArr (rendezvous_initialized γtq).

Let cancellation_handle := cell_cancellation_handle _ _ array_spec NArr.
Let cell_cancelled := cell_is_cancelled _ _ array_spec NArr.

Definition resources_for_resumer T γf γd i: iProp :=
  ((future_completion_permit γf 1%Qp ∨
    future_completion_permit γf (1/2)%Qp ∗ iterator_issued γd i) ∗ T ∨
   future_completion_permit γf 1%Qp ∗ iterator_issued γd i).

Definition cell_resources
           γtq γa γe γd i (k: option cellState) (insideDeqFront: bool):
  iProp :=
  match k with
  | None => E ∗ if insideDeqFront then R else True%I
  | Some (cellPassedValue v d) =>
    iterator_issued γd i ∗
    cancellation_handle γa i ∗
    ⌜lit_is_unboxed v⌝ ∧
    ∃ ℓ, cell_location γtq γa i ℓ ∗
         match d with
         | None => ℓ ↦ SOMEV #v ∗ E ∗ V v ∗ R
         | Some cellRendezvousSucceeded =>
           ℓ ↦ SOMEV #v ∗ cell_breaking_token γtq i ∗ V v ∗ R ∨
           ℓ ↦ TAKENV ∗ iterator_issued γe i ∗ (E ∨ cell_breaking_token γtq i)
         | Some cellBroken => ℓ ↦ BROKENV ∗ (E ∗ CB ∨ iterator_issued γe i)
         end
  | Some (cellInhabited γf f r) =>
    iterator_issued γe i ∗ rendezvous_thread_handle γtq γf f i ∗
    ∃ ℓ, cell_location γtq γa i ℓ ∗
         match r with
         | None => ℓ ↦ InjLV f ∗ cancellation_handle γa i ∗
                  E ∗ (if insideDeqFront then R else True) ∗
                  future_cancellation_permit γf (1/2)%Qp ∗
                  (future_completion_permit γf 1%Qp ∨
                   future_completion_permit γf (1/2)%Qp ∗
                   iterator_issued γd i)
         | Some (cellResumed v) =>
           (ℓ ↦ InjLV f ∨ ℓ ↦ RESUMEDV) ∗
           iterator_issued γd i ∗
           future_is_completed γf #v ∗
           cancellation_handle γa i ∗
           future_cancellation_permit γf (1/2)%Qp
         | Some cellImmediatelyCancelled =>
           (ℓ ↦ InjLV f ∨ ℓ ↦ CANCELLEDV) ∗
           ⌜immediateCancellation⌝ ∗
           future_is_cancelled γf ∗
           resources_for_resumer (if insideDeqFront then R else True) γf γd i
         | Some (cellCancelled d) =>
           future_is_cancelled γf ∗
           ⌜¬ immediateCancellation⌝ ∗
           match d with
           | None =>
             cancellation_handle γa i ∗
             (if insideDeqFront then R else True) ∗
             (ℓ ↦ InjLV f ∗ E ∗
                (future_completion_permit γf 1%Qp ∨
                 future_completion_permit γf (1/2)%Qp ∗ iterator_issued γd i)
              ∨ ⌜insideDeqFront⌝ ∧
                ∃ v, ⌜lit_is_unboxed v⌝ ∧
                     ℓ ↦ SOMEV #v ∗ iterator_issued γd i ∗
                       future_completion_permit γf 1%Qp ∗ V v)
           | Some cancellationPrevented =>
             ⌜insideDeqFront⌝ ∧
             cancellation_handle γa i ∗
             (ℓ ↦ InjLV f ∗ E ∗
                (future_completion_permit γf 1%Qp ∨
                 future_completion_permit γf (1/2)%Qp ∗ iterator_issued γd i)
              ∨ ℓ ↦ REFUSEDV ∗ resources_for_resumer ERefuse γf γd i
                  ∗ cell_cancelling_token γtq i
              ∨ ∃ v, ⌜lit_is_unboxed v⌝ ∧
                     ℓ ↦ SOMEV #v ∗ iterator_issued γd i ∗
                     future_completion_permit γf 1%Qp ∗ V v)
           | Some (cancellationAllowed d) =>
             match d with
             | None =>
               ℓ ↦ InjLV f ∗ E ∗
               resources_for_resumer
                 (if insideDeqFront then awakening_permit γtq else True) γf γd i
             | Some (cellTookValue v) =>
               (ℓ ↦ SOMEV #v ∗ ⌜lit_is_unboxed v⌝ ∗ V v ∗ awakening_permit γtq ∨
                ℓ ↦ CANCELLEDV ∗ cell_cancelling_token γtq i) ∗
                 iterator_issued γd i ∗
                 future_completion_permit γf 1%Qp
             | Some cellClosed =>
               ℓ ↦ CANCELLEDV ∗
                 cell_cancelling_token γtq i ∗
                 resources_for_resumer
                   (if insideDeqFront then awakening_permit γtq else True) γf γd i
             end
           end
         end
  end.

Definition is_skippable (r: option cellState): bool :=
  match r with
  | Some (cellInhabited
            γt th (Some (cellCancelled (Some (cancellationAllowed _))))) =>
    true
  | _ => false
  end.

Definition is_nonskippable (r: option cellState): bool :=
  negb (is_skippable r).

Definition is_immediately_cancelled (r: option cellState): bool :=
  match r with
  | Some (cellInhabited γt th (Some cellImmediatelyCancelled)) => true
  | _ => false
  end.

Definition cell_list_contents_auth_ra l (deqFront: nat): algebra :=
  ● (length l, (deqFront, MaxNat deqFront),
     (map (option_map cellState_ra) l,
      Excl' (count_matching is_nonskippable (drop deqFront l)))).

Lemma rendezvous_state_included γ l deqFront i s:
  own γ (cell_list_contents_auth_ra l deqFront) -∗
  rendezvous_state γ i s -∗
  ⌜∃ c, l !! i = Some c ∧ s ≼ option_map cellState_ra c⌝.
Proof.
  iIntros "H● H◯".
  iDestruct (own_valid_2 with "H● H◯")
    as %[[_ [(v&HEl&HInc)%list_singletonM_included _]%prod_included
         ]%prod_included _]%auth_both_valid.
  simpl in *. iPureIntro.
  rewrite map_lookup in HEl.
  destruct (l !! i) as [el|]; simpl in *; simplify_eq.
  eexists. by split.
Qed.

Lemma rendezvous_state_included' γ l deqFront i s:
  own γ (cell_list_contents_auth_ra l deqFront) -∗
  rendezvous_state γ i (Some s) -∗
  ⌜∃ c, l !! i = Some (Some c) ∧ s ≼ cellState_ra c⌝.
Proof.
  iIntros "H● H◯".
  iDestruct (rendezvous_state_included with "H● H◯") as %(c & HEl & HInc).
  iPureIntro.
  destruct c as [el|]; last by apply included_None in HInc.
  simpl in *. eexists. split; first done. move: HInc.
  rewrite Some_included.
  case; last done. intros ->.
  destruct el as [v r|γth f r]; simpl.
  + by apply Cinl_included.
  + by apply Cinr_included.
Qed.

Lemma thread_queue_state_valid γtq n l deqFront:
  own γtq (cell_list_contents_auth_ra l deqFront) -∗
  thread_queue_state γtq n -∗
  ⌜n = count_matching is_nonskippable (drop deqFront l)⌝.
Proof.
  iIntros "H● HState".
  iDestruct (own_valid_2 with "H● HState")
    as %[[_ [_ HEq%Excl_included]%prod_included]%prod_included
                                                _]%auth_both_valid.
  by simplify_eq.
Qed.

Theorem cell_list_contents_ra_locs γ l deqFront i γt th:
  own γ (cell_list_contents_auth_ra l deqFront) -∗
  rendezvous_thread_locs_state γ γt th i -∗
  ⌜exists c, l !! i = Some (Some (cellInhabited γt th c))⌝.
Proof.
  iIntros "H● H◯".
  iDestruct (rendezvous_state_included' with "H● H◯") as %([|] & HEl & HInc).
  all: iPureIntro; simpl in *.
  - exfalso. move: HInc. rewrite csum_included. case; first done.
    case.
    * by intros (? & ? & HContra & _).
    * by intros (? & ? & ? & HContra & _).
  - move: HInc. rewrite Cinr_included prod_included=> /=. case.
    rewrite to_agree_included. case=>/=. intros <- <- _.
    by eexists.
Qed.

Definition cell_enqueued γtq (i: nat): iProp :=
  rendezvous_state γtq i ε.

Theorem cell_enqueued_lookup γtq l i d:
  own γtq (cell_list_contents_auth_ra l d) -∗
  cell_enqueued γtq i -∗
  ⌜exists v, l !! i = Some v⌝.
Proof.
  iIntros "H● HExistsEl".
  iDestruct (rendezvous_state_included with "H● HExistsEl") as %(c & HEl & _).
  iPureIntro. eauto.
Qed.

Definition thread_queue_invariant γa γtq γe γd l deqFront: iProp :=
  own γtq (cell_list_contents_auth_ra l deqFront) ∗
      ([∗ list] i ↦ e ∈ l, cell_resources γtq γa γe γd i e
                                          (bool_decide (i < deqFront))) ∗
      ⌜deqFront ≤ length l⌝ ∧
  ⌜deqFront > 0 ∧ (∃ r, l !! (deqFront - 1)%nat = Some r ∧ is_skippable r)
  -> False⌝.

Definition is_thread_queue γa γtq γe γd e d :=
  let co := rendezvous_initialized γtq in
  (inv NTq (∃ l deqFront, thread_queue_invariant γa γtq γe γd l deqFront) ∗
   is_infinite_array _ _ array_spec NArr γa co ∗
   is_iterator _ array_spec NArr NEnq co γa (suspension_permit γtq) γe e ∗
   is_iterator _ array_spec NArr NDeq co γa (awakening_permit γtq) γd d)%I.

Theorem newThreadQueue_spec:
  {{{ inv_heap_inv }}}
    newThreadQueue array_interface #()
  {{{ γa γtq γe γd e d, RET (e, d); is_thread_queue γa γtq γe γd e d
      ∗ thread_queue_state γtq 0 }}}.
Proof.
  iIntros (Φ) "HHeap HΦ". wp_lam. wp_bind (newInfiniteArray _ _).
  rewrite -fupd_wp.
  iMod (own_alloc (cell_list_contents_auth_ra [] 0
                   ⋅ ◯ (ε, (ε, Excl' 0)))) as (γtq) "[H● H◯]".
  { apply auth_both_valid. split=> /=.
    - apply pair_included. split; first by apply ucmra_unit_least.
      apply pair_included. split; first by apply ucmra_unit_least.
      done.
    - apply pair_valid. split; first done.
      apply pair_valid. split; last done. apply list_lookup_valid.
      by case. }
  replace 2%Z with (Z.of_nat 2); last lia.
  iApply (newInfiniteArray_spec with "[HHeap]").
  { iSplitR. by iPureIntro; lia. done. }
  iIntros "!> !>" (γa aℓ) "[HArr (HE & HD & _)]". wp_pures.
  wp_bind (newIterator _ _).
  replace 0%Z with (Z.of_nat 0); last lia.
  iApply (newIterator_spec with "[HD]"); first by simpl; iFrame.
  iIntros "!>" (γd d) "HDeq".
  wp_bind (newIterator _ _). wp_pures. rewrite -wp_fupd.
  iApply (newIterator_spec with "[HE]"); first by simpl; iFrame.
  iIntros "!>" (γe e) "HEnq".
  iMod (inv_alloc NTq _
        (∃ l deqFront, thread_queue_invariant γa γtq γe γd l deqFront)
       with "[H●]") as "#HInv".
  { iExists [], 0. iFrame. simpl. iPureIntro. repeat (split; first done).
    case. lia. }
  iSpecialize ("HΦ" $! γa γtq γe γd e d).
  iModIntro. wp_pures. iApply "HΦ". by iFrame.
Qed.

Theorem thread_queue_append γtq γa γe γd n l deqFront:
  ▷ E -∗ thread_queue_state γtq n -∗
  ▷ thread_queue_invariant γa γtq γe γd l deqFront ==∗
  ▷ (suspension_permit γtq ∗ cell_enqueued γtq (length l) ∗
  thread_queue_state γtq (S n) ∗
  thread_queue_invariant γa γtq γe γd (l ++ [None]) deqFront).
Proof.
  iIntros "HE H◯ (>H● & HRRs & >HLen & >HDeqIdx)".
  iDestruct (thread_queue_state_valid with "H● H◯") as %->.
  iDestruct "HLen" as %HLen.
  iMod (own_update_2 with "H● H◯") as "[H● [[$ $] $]]".
  2: {
    rewrite /thread_queue_invariant app_length big_sepL_app=>/=.
    iFrame "HE H● HRRs".
    iSplitR; first by rewrite bool_decide_false; last lia.
    iDestruct "HDeqIdx" as %HDeqIdx. iPureIntro.
    split; first lia. intros [HContra1 HContra2].
    rewrite lookup_app_l in HContra2; last lia.
    auto.
  }
  {
    apply auth_update, prod_local_update'; last apply prod_local_update'=> /=.
    * rewrite app_length=>/=.
      apply prod_local_update_1=>/=.
      by apply nat_local_update.
    * rewrite map_app=> /=.
      replace (length l) with (length (map (option_map cellState_ra) l))
        by rewrite map_length //.
      rewrite ucmra_unit_right_id.
      apply list_append_local_update=> ?.
      apply list_lookup_validN. by case.
    * etransitivity.
      by apply delete_option_local_update, _.
      rewrite drop_app_le; last lia. rewrite count_matching_app=>/=.
      rewrite Nat.add_1_r.
      by apply alloc_option_local_update.
  }
Qed.

Theorem thread_queue_append' E' γtq γa γe γd n e d:
  ↑NTq ⊆ E' ->
  is_thread_queue γa γtq γe γd e d -∗
  ▷ E -∗ ▷ thread_queue_state γtq n ={E'}=∗
  thread_queue_state γtq (S n) ∗ suspension_permit γtq.
Proof.
  iIntros (HMask) "[HInv _] HE >HState".
  iInv "HInv" as (l deqFront) "HOpen" "HClose".
  iMod (thread_queue_append with "HE HState HOpen") as "(>$ & _ & >$ & HRest)".
  iMod ("HClose" with "[HRest]") as "_"; last done. by iExists _, _.
Qed.

Global Instance deq_front_at_least_persistent γtq n:
  Persistent (deq_front_at_least γtq n).
Proof. apply _. Qed.

Theorem deq_front_at_least_valid γtq n l deqFront :
  own γtq (cell_list_contents_auth_ra l deqFront) -∗
  deq_front_at_least γtq n -∗
  ⌜n <= deqFront⌝.
Proof.
  iIntros "H● H◯".
  iDestruct (own_valid_2 with "H● H◯") as %[HValid _]%auth_both_valid.
  apply prod_included in HValid. destruct HValid as [HValid _].
  apply prod_included in HValid. destruct HValid as [_ HValid].
  apply prod_included in HValid. destruct HValid as [_ HValid].
  apply max_nat_included in HValid. simpl in *.
  iPureIntro; simpl in *; lia.
Qed.

Theorem cell_list_contents__deq_front_at_least i γtq l deqFront:
  (i <= deqFront)%nat ->
  own γtq (cell_list_contents_auth_ra l deqFront) ==∗
  own γtq (cell_list_contents_auth_ra l deqFront) ∗
  deq_front_at_least γtq i.
Proof.
  iIntros (HLe) "H●".
  iMod (own_update with "H●") as "[$ $]"; last done.
  apply auth_update_core_id.
  by apply _.
  repeat (apply prod_included; split); simpl.
  all: try apply ucmra_unit_least.
  apply max_nat_included. simpl. lia.
Qed.

Lemma cell_breaking_token_exclusive γtq i:
  cell_breaking_token γtq i -∗ cell_breaking_token γtq i -∗ False.
Proof.
  iIntros "HCb1 HCb2".
  iDestruct "HCb1" as (?) "HCb1". iDestruct "HCb2" as (?) "HCb2".
  iCombine "HCb1" "HCb2" as "HCb". rewrite list_singletonM_op.
  iDestruct (own_valid with "HCb") as %[_ [HValid _]%pair_valid]%pair_valid.
  exfalso. move: HValid=> /=. rewrite list_singletonM_valid.
  case=> _/=. case=>/=. case.
Qed.

Lemma None_op_right_id (A: cmraT) (a: option A): a ⋅ None = a.
Proof. by destruct a. Qed.

Lemma cell_list_contents_cell_update_alloc s
      γtq l deqFront i initialState newState:
  l !! i = Some initialState ->
  is_nonskippable initialState = is_nonskippable newState ->
  (Some (option_map cellState_ra initialState), None) ~l~>
  (Some (option_map cellState_ra newState),
   Some s) ->
  own γtq (cell_list_contents_auth_ra l deqFront) ==∗
  own γtq (cell_list_contents_auth_ra (<[i := newState]> l) deqFront) ∗
  rendezvous_state γtq i s.
Proof.
  iIntros (HEl HNonSkippable HUp) "H●".
  iMod (own_update with "H●") as "($ & $)"; last done.
  apply auth_update_alloc. rewrite insert_length.
  apply prod_local_update_2, prod_local_update=> /=.
  - rewrite -!fmap_is_map list_fmap_insert.
    apply list_lookup_local_update=> i'. rewrite lookup_nil.
    destruct (lt_eq_lt_dec i' i) as [[HLt| ->]|HGt].
    + rewrite list_lookup_singletonM_lt; last lia.
      rewrite list_lookup_insert_ne; last lia.
      rewrite map_lookup.
      assert (is_Some (l !! i')) as [? ->].
      { apply lookup_lt_is_Some. apply lookup_lt_Some in HEl. lia. }
      apply option_local_update'''. by rewrite ucmra_unit_left_id.
      intros n. by rewrite ucmra_unit_left_id.
    + rewrite list_lookup_singletonM list_lookup_insert.
      2: { eapply lookup_lt_Some. by rewrite map_lookup HEl. }
      by rewrite map_lookup HEl=> /=.
    + rewrite list_lookup_singletonM_gt; last lia.
      rewrite list_lookup_insert_ne; last lia.
      done.
  - rewrite !count_matching_is_sum_map -!fmap_is_map !fmap_drop.
    rewrite list_fmap_insert=> /=. rewrite list_insert_id; first done.
    rewrite map_lookup HEl /= HNonSkippable //.
Qed.

Lemma inhabit_cell_ra γtq l deqFront i γf f:
  l !! i = Some None ->
  own γtq (cell_list_contents_auth_ra l deqFront) ==∗
  own γtq (cell_list_contents_auth_ra
             (<[i := Some (cellInhabited γf f None)]> l) deqFront) ∗
  rendezvous_thread_locs_state γtq γf f i.
Proof.
  iIntros (HEl) "H●".
  iMod (cell_list_contents_cell_update_alloc with "H●") as "($ & $)"; try done.
  apply option_local_update'''.
  by rewrite None_op_right_id.
  intros n. by rewrite None_op_right_id.
Qed.

Lemma rendezvous_state_op γtq i a b:
  rendezvous_state γtq i a ∗ rendezvous_state γtq i b ⊣⊢
  rendezvous_state γtq i (a ⋅ b).
Proof.
  rewrite /rendezvous_state -own_op -auth_frag_op -pair_op.
  rewrite ucmra_unit_left_id -pair_op list_singletonM_op //.
Qed.

Lemma fill_cell_ra γtq l deqFront i v:
  l !! i = Some None ->
  own γtq (cell_list_contents_auth_ra l deqFront) ==∗
  own γtq (cell_list_contents_auth_ra
             (<[i := Some (cellPassedValue v None)]> l) deqFront) ∗
  rendezvous_state γtq i (Some (Cinl (to_agree #v, ε))) ∗
  cell_breaking_token γtq i.
Proof.
  iIntros (HEl) "H●".
  iMod (cell_list_contents_cell_update_alloc with "H●") as "($ & H◯)"=>//=.
  { apply option_local_update'''. by rewrite None_op_right_id.
    intros n. by rewrite None_op_right_id. }

  iAssert (rendezvous_state γtq i (Some (Cinl (to_agree #v, ε))))
    with "[H◯]" as "#$".
  { iApply (own_mono with "H◯"). rewrite auth_included; split=> //=.
    do 2 (rewrite prod_included; split=>//=). rewrite list_singletonM_included.
    eexists. rewrite list_lookup_singletonM. split; first done.
    rewrite Some_included Cinl_included prod_included /=. right. split=>//=.
    apply ucmra_unit_least.
  }
  by iExists _.
Qed.

Lemma take_cell_value_ra γtq l deqFront i v:
  l !! i = Some (Some (cellPassedValue v None)) ->
  own γtq (cell_list_contents_auth_ra l deqFront) ==∗
  own γtq (cell_list_contents_auth_ra
             (<[i := Some (cellPassedValue v (Some cellRendezvousSucceeded))]> l) deqFront) ∗
  rendezvous_state γtq i (Some (Cinl (to_agree #v, (None, Some (to_agree true))))).
Proof.
  iIntros (HEl) "H●".
  iMod (cell_list_contents_cell_update_alloc with "H●") as "[$ $]"=> //=.
  apply option_local_update'''=> [|n];
    by rewrite -Some_op -Cinl_op -!pair_op None_op_right_id agree_idemp.
Qed.

Lemma cell_list_contents_cell_update newState initialState s s'
      γtq l deqFront i:
  l !! i = Some initialState ->
  is_nonskippable initialState = is_nonskippable newState ∨
  i < deqFront ->
  (option_map cellState_ra initialState, s) ~l~>
  (option_map cellState_ra newState, s') ->
  own γtq (cell_list_contents_auth_ra l deqFront) -∗
  rendezvous_state γtq i s ==∗
  own γtq (cell_list_contents_auth_ra (<[i := newState]> l) deqFront) ∗
  rendezvous_state γtq i s'.
Proof.
  iIntros (HEl HNonSkippable HUp) "H● H◯".
  iMod (own_update_2 with "H● H◯") as "($ & $)"; last done.
  apply auth_update. rewrite insert_length.
  apply prod_local_update_2, prod_local_update=> /=.
  - rewrite -!fmap_is_map list_fmap_insert.
    apply list_lookup_local_update=> i'.
    destruct (lt_eq_lt_dec i' i) as [[HLt| ->]|HGt].
    + rewrite !list_lookup_singletonM_lt; try lia.
      rewrite list_lookup_insert_ne; last lia.
      by rewrite map_lookup.
    + rewrite !list_lookup_singletonM list_lookup_insert.
      2: { eapply lookup_lt_Some. by rewrite map_lookup HEl. }
      rewrite map_lookup HEl=> /=.
      apply option_local_update, HUp.
    + rewrite !list_lookup_singletonM_gt; try lia.
      rewrite list_lookup_insert_ne; last lia.
      done.
  - destruct HNonSkippable as [HNonSkippable|HDeqFront].
    * rewrite !count_matching_is_sum_map -!fmap_is_map !fmap_drop.
      rewrite list_fmap_insert=> /=. rewrite list_insert_id; first done.
      rewrite map_lookup HEl /= HNonSkippable //.
    * by rewrite drop_insert_gt; last lia.
Qed.

Lemma abandon_cell_ra γtq l deqFront i γf f:
  l !! i = Some (Some (cellInhabited γf f (Some (cellCancelled None)))) ->
  own γtq (cell_list_contents_auth_ra l deqFront) -∗
  cancellation_registration_token γtq i ==∗
  own γtq (cell_list_contents_auth_ra
             (<[i := Some (cellInhabited γf f (Some (cellCancelled (Some cancellationPrevented))))]> l) deqFront) ∗
  rendezvous_state γtq i (Some (Cinr (to_agree (γf, f), Some (Cinr (Cinr (1, ε)))))) ∗
  rendezvous_state γtq i (Some (Cinr (to_agree (γf, f), Some (Cinr (Cinr (ε, Some (Cinl (to_agree ())))))))).
Proof.
  iIntros (HEl) "H● H◯". iDestruct "H◯" as (? ?) "H◯".
  rewrite rendezvous_state_op.
  iMod (cell_list_contents_cell_update with "H● H◯") as "($ & $)"=>//.
  by left.
  simpl.
  apply option_local_update, csum_local_update_r.
  apply prod_local_update=> /=.
  * apply local_update_total_valid=> _ _. rewrite to_agree_included=> ?.
    simplify_eq. by rewrite agree_idemp.
  * apply option_local_update; do 2 apply csum_local_update_r.
    apply prod_local_update=> /=.
    by apply nat_local_update.
    by apply alloc_option_local_update.
Qed.

Lemma finish_cancellation_ra γtq γf f l deqFront i:
  l !! i = Some (Some (cellInhabited γf f (Some (cellCancelled (Some (cancellationAllowed None)))))) ->
  own γtq (cell_list_contents_auth_ra l deqFront) ==∗
  own γtq (cell_list_contents_auth_ra
             (<[i := Some (cellInhabited γf f (Some (cellCancelled (Some (cancellationAllowed (Some cellClosed))))))]> l) deqFront) ∗
  rendezvous_state γtq i (Some (Cinr (to_agree (γf, f), Some (Cinr (Cinr (ε, Some (Cinr (Some (Cinr (to_agree ())))))))))).
Proof.
  iIntros (HEl) "H●".
  iMod (cell_list_contents_cell_update_alloc with "H●") as "($ & $)"=> //=.
  apply option_local_update'''=> [|n].
  by rewrite -Some_op -Cinr_op -!pair_op !agree_idemp.
  rewrite -Some_op -Cinr_op -!pair_op !agree_idemp -Some_op -!Cinr_op.
  by rewrite -pair_op -Some_op -Cinr_op None_op_right_id.
Qed.

Lemma break_cell_ra γtq l deqFront i v:
  l !! i = Some (Some (cellPassedValue v None)) ->
  own γtq (cell_list_contents_auth_ra l deqFront) -∗
  cell_breaking_token γtq i ==∗
  own γtq (cell_list_contents_auth_ra
             (<[i := Some (cellPassedValue v (Some cellBroken))]> l) deqFront) ∗
  rendezvous_state γtq i (Some (Cinl (to_agree #v, (None, Some (to_agree false))))).
Proof.
  iIntros (HEl) "H● H◯". iDestruct "H◯" as (?) "H◯".
  iMod (cell_list_contents_cell_update with "H● H◯") as "($ & $)"=>//.
  by left.
  apply option_local_update, csum_local_update_l.
  apply prod_local_update=> /=; last apply prod_local_update=> /=.
  * apply local_update_total_valid=> _ _. rewrite to_agree_included=> ?.
    by simplify_eq.
  * apply delete_option_local_update. apply _.
  * apply alloc_option_local_update. done.
Qed.

Lemma cancel_cell_ra γtq γf f l deqFront i:
  l !! i = Some (Some (cellInhabited γf f None)) ->
  own γtq (cell_list_contents_auth_ra l deqFront) ==∗
  own γtq (cell_list_contents_auth_ra
             (<[i := Some (cellInhabited γf f (Some (cellCancelled None)))]> l) deqFront) ∗
  rendezvous_state γtq i (Some (Cinr (to_agree (γf, f), Some (Cinr (Cinr (2, ε)))))).
Proof.
  iIntros (HEl) "H●".
  iMod (cell_list_contents_cell_update_alloc with "H●") as "($ & $)"=> //=.
  apply option_local_update'''=> [|n];
    by rewrite -Some_op -Cinr_op -!pair_op None_op_right_id !agree_idemp.
Qed.

Lemma immediately_cancel_cell_ra γtq γf f l deqFront i:
  l !! i = Some (Some (cellInhabited γf f None)) ->
  own γtq (cell_list_contents_auth_ra l deqFront) ==∗
  own γtq (cell_list_contents_auth_ra
             (<[i := Some (cellInhabited γf f (Some cellImmediatelyCancelled))]> l) deqFront) ∗
  rendezvous_state γtq i (Some (Cinr (to_agree (γf, f), Some (Cinr (Cinl (to_agree ())))))).
Proof.
  iIntros (HEl) "H●".
  iMod (cell_list_contents_cell_update_alloc with "H●") as "($ & $)"=> //=.
  apply option_local_update'''=> [|n];
    by rewrite -Some_op -Cinr_op -!pair_op None_op_right_id !agree_idemp.
Qed.

Lemma resumed_cell_core_id_ra γtq γf f l deqFront i v:
  l !! i = Some (Some (cellInhabited γf f (Some (cellResumed v)))) ->
  own γtq (cell_list_contents_auth_ra l deqFront) ==∗
  own γtq (cell_list_contents_auth_ra l deqFront) ∗
  rendezvous_state γtq i (Some (Cinr (to_agree (γf, f),
                                      Some (Cinl (to_agree #v))))).
Proof.
  iIntros (HEl) "H●".
  iMod (cell_list_contents_cell_update_alloc with "H●") as "(H● & $)"=> //=.
  2: by rewrite list_insert_id.
  apply option_local_update'''=> [|n];
    by rewrite -Some_op -Cinr_op -!pair_op -Some_op -Cinl_op !agree_idemp.
Qed.

Lemma cancelled_cell_core_id_ra γtq γf f l deqFront i r:
  l !! i = Some (Some (cellInhabited γf f (Some (cellCancelled r)))) ->
  own γtq (cell_list_contents_auth_ra l deqFront) ==∗
  own γtq (cell_list_contents_auth_ra l deqFront) ∗
  rendezvous_state γtq i (Some (Cinr (to_agree (γf, f),
                                      Some (Cinr (Cinr ε))))).
Proof.
  iIntros (HEl) "H●".
  iMod (cell_list_contents_cell_update_alloc with "H●") as "(H● & $)"=> //=.
  2: by rewrite list_insert_id.
  apply option_local_update'''=> [|n];
    by rewrite -Some_op -Cinr_op -!pair_op -Some_op agree_idemp -!Cinr_op
            ucmra_unit_left_id.
Qed.

Lemma resume_cell_ra γtq γf f l deqFront i v:
  l !! i = Some (Some (cellInhabited γf f None)) ->
  own γtq (cell_list_contents_auth_ra l deqFront) ==∗
  own γtq (cell_list_contents_auth_ra
             (<[i := Some (cellInhabited γf f (Some (cellResumed v)))]> l) deqFront) ∗
  rendezvous_state γtq i (Some (Cinr (to_agree (γf, f), Some (Cinl (to_agree #v))))).
Proof.
  iIntros (HEl) "H●".
  iMod (cell_list_contents_cell_update_alloc with "H●") as "($ & $)"=> //=.
  apply option_local_update'''=> [|n];
    by rewrite -Some_op -Cinr_op -!pair_op None_op_right_id !agree_idemp.
Qed.

Lemma awakening_permit_combine γtq n:
  n > 0 ->
  ([∗] replicate n (awakening_permit γtq))%I ≡ own γtq (◯ (ε, (n, ε), ε)).
Proof.
  move=> Hn.
  rewrite big_opL_replicate_irrelevant_element -big_opL_own;
    last by inversion Hn.
  move: (big_opL_op_prodR 0)=> /= HBigOpL.
  rewrite -big_opL_auth_frag !HBigOpL !big_opL_op_ucmra_unit.
  rewrite -big_opL_op_nat' Nat.mul_1_r replicate_length.
  done.
Qed.

Lemma suspension_permit_combine γtq n:
  n > 0 ->
  ([∗] replicate n (suspension_permit γtq))%I ≡ own γtq (◯ (n, ε, ε)).
Proof.
  move=> Hn.
  rewrite big_opL_replicate_irrelevant_element -big_opL_own;
    last by inversion Hn.
  move: (big_opL_op_prodR 0)=> /= HBigOpL.
  rewrite -big_opL_auth_frag !HBigOpL !big_opL_op_ucmra_unit.
  rewrite -big_opL_op_nat' Nat.mul_1_r replicate_length.
  done.
Qed.

Lemma deque_register_ra_update γ l deqFront i n:
  (i + deqFront < length l)%nat ->
  own γ (cell_list_contents_auth_ra l deqFront) -∗
  thread_queue_state γ n ==∗
  own γ (cell_list_contents_auth_ra l (deqFront + S i))
  ∗ [∗] replicate (S i) (awakening_permit γ)
  ∗ thread_queue_state γ
      (n - count_matching is_nonskippable (take (S i) (drop deqFront l)))
  ∗ deq_front_at_least γ (deqFront + S i).
Proof.
  rewrite awakening_permit_combine; last lia.
  iIntros (?) "H● H◯".
  iMod (own_update_2 with "H● H◯") as "($ & $ & $ & $)"; last done.
  apply auth_update, prod_local_update=>/=.
  apply prod_local_update_2, prod_local_update=>/=.
  - rewrite ucmra_unit_right_id. by apply nat_local_update.
  - apply max_nat_local_update; simpl; lia.
  - apply prod_local_update_2. rewrite ucmra_unit_right_id=>/=.
    apply local_update_total_valid=> _ _. rewrite Excl_included=> ->.
    etransitivity. by apply delete_option_local_update, _.
    rewrite count_matching_take.
    assert (∀ n m, m ≤ n -> n - (n - m) = m) as HPure by lia.
    rewrite HPure.
    + rewrite drop_drop. by apply alloc_option_local_update.
    + rewrite count_matching_drop. lia.
Qed.

Lemma allow_cell_cancellation_inside_deqFront_ra
      γ l deqFront i j n γf f:
  let l' := <[j := Some (cellInhabited γf f (Some (cellCancelled (Some (cancellationAllowed None)))))]> l in
  find_index is_nonskippable (drop deqFront l') = Some i ->
  j < deqFront ->
  l !! j = Some (Some (cellInhabited γf f (Some (cellCancelled None)))) ->
  own γ (cell_list_contents_auth_ra l deqFront) -∗
  thread_queue_state γ n -∗
  cancellation_registration_token γ j ==∗
  own γ (cell_list_contents_auth_ra l' (deqFront + S i))
  ∗ [∗] replicate (S i) (awakening_permit γ)
  ∗ thread_queue_state γ (n - 1)
  ∗ deq_front_at_least γ (deqFront + S i)
  ∗ rendezvous_state γ j (Some (Cinr (to_agree (γf, f), Some (Cinr (Cinr (1, ε))))))
  ∗ rendezvous_state γ j (Some (Cinr (to_agree (γf, f), Some (Cinr (Cinr (ε, Some (Cinr ε))))))).
Proof.
  iIntros (l' HFindSome HDeqFront HEl) "H● H◯1 H◯2".
  iDestruct "H◯2" as (? ?) "H◯2".
  rewrite rendezvous_state_op.
  iMod (cell_list_contents_cell_update with "H● H◯2") as "[H● $]"; try done.
  by right.
  2: {
    iMod (deque_register_ra_update with "H● H◯1") as "($ & $ & H◯ & $)".
    - apply find_index_Some in HFindSome.
      destruct HFindSome as [(v & HEl' & _) _].
      eapply lookup_lt_Some. by rewrite Nat.add_comm -lookup_drop.
    - by move: (present_cells_in_take_Si_if_next_present_is_Si _ _ _ HFindSome)
        => ->.
  }
  simpl.
  apply option_local_update, csum_local_update_r.
  apply prod_local_update=> /=.
  * apply local_update_total_valid=> _ _. rewrite to_agree_included=> ?.
    simplify_eq. by rewrite agree_idemp.
  * apply option_local_update; do 2 apply csum_local_update_r.
    apply prod_local_update=> /=.
    by apply nat_local_update.
    by apply alloc_option_local_update.
Qed.

Lemma allow_cell_cancellation_outside_deqFront_ra
      γ l deqFront j n γf f:
  let l' := <[j := Some (cellInhabited γf f (Some (cellCancelled (Some (cancellationAllowed None)))))]> l in
  deqFront ≤ j ->
  l !! j = Some (Some (cellInhabited γf f (Some (cellCancelled None)))) ->
  own γ (cell_list_contents_auth_ra l deqFront) -∗
  thread_queue_state γ n -∗
  cancellation_registration_token γ j ==∗
  own γ (cell_list_contents_auth_ra l' deqFront)
  ∗ thread_queue_state γ (n - 1)
  ∗ rendezvous_state γ j (Some (Cinr (to_agree (γf, f), Some (Cinr (Cinr (1, ε))))))
  ∗ rendezvous_state γ j (Some (Cinr (to_agree (γf, f), Some (Cinr (Cinr (ε, Some (Cinr ε))))))).
Proof.
  iIntros (l' HDeqFront HEl) "H● H◯1 H◯2".
  iDestruct "H◯2" as (? ?) "H◯2". iCombine "H◯1" "H◯2" as "H◯".
  iMod (own_update_2 with "H● H◯") as "($ & $ & $ & $)"; last done.
  apply auth_update. rewrite insert_length.
  apply prod_local_update_2, prod_local_update=> /=.
  - rewrite -!fmap_is_map list_fmap_insert.
    apply list_lookup_local_update=> i'.
    rewrite list_singletonM_op. simpl.
    destruct (lt_eq_lt_dec i' j) as [[HLt| ->]|HGt].
    + rewrite !list_lookup_singletonM_lt; try lia.
      rewrite list_lookup_insert_ne; last lia.
      by rewrite map_lookup.
    + rewrite !list_lookup_singletonM list_lookup_insert.
      2: { eapply lookup_lt_Some. by rewrite map_lookup HEl. }
      rewrite map_lookup HEl=> /=.
      apply option_local_update, option_local_update, csum_local_update_r.
      apply prod_local_update=>/=.
      * apply local_update_total_valid=> _ _. rewrite to_agree_included=> ?.
        simplify_eq. by rewrite agree_idemp.
      * apply option_local_update; do 2 apply csum_local_update_r.
        apply prod_local_update=> /=.
        by apply nat_local_update.
        by apply alloc_option_local_update.
    + rewrite !list_lookup_singletonM_gt; try lia.
      rewrite list_lookup_insert_ne; last lia.
      done.
  - apply local_update_total_valid=> _ _. rewrite Excl_included=> ?.
    simplify_eq. etransitivity. apply delete_option_local_update. by apply _.
    rewrite drop_insert_le; last lia. rewrite list_insert_alter.
    erewrite count_matching_alter.
    2: { rewrite lookup_drop. replace (_ + _) with j by lia. done. }
    simpl. rewrite Nat.add_0_r.
    by apply alloc_option_local_update.
Qed.

Lemma put_value_in_cancelled_cell_ra v γtq γf f l deqFront i:
  l !! i = Some (Some (cellInhabited γf f (Some (cellCancelled (Some (cancellationAllowed None)))))) ->
  own γtq (cell_list_contents_auth_ra l deqFront) ==∗
  own γtq (cell_list_contents_auth_ra
             (<[i := Some (cellInhabited γf f (Some (cellCancelled (Some (cancellationAllowed (Some (cellTookValue v)))))))]> l) deqFront) ∗
  rendezvous_state γtq i (Some (Cinr (to_agree (γf, f), Some (Cinr (Cinr (ε, Some (Cinr (Some (Cinl (to_agree #v)))))))))).
Proof.
  iIntros (HEl) "H●".
  iMod (cell_list_contents_cell_update_alloc with "H●") as "($ & H◯)"=>//=.
  apply option_local_update'''.
  by rewrite -Some_op -Cinr_op -pair_op agree_idemp.
  intros n. rewrite -Some_op -Cinr_op -pair_op agree_idemp -Some_op -Cinr_op.
  by rewrite -Cinr_op -pair_op -Some_op -Cinr_op None_op_right_id.
Qed.

Lemma advance_deqFront i deqFront l γtq γa γe γd:
  find_index is_nonskippable (drop deqFront l) = Some i ->
  [∗] replicate i (awakening_permit γtq) -∗
  ▷ R -∗
  ▷ ([∗ list] k ↦ y ∈ l, cell_resources γtq γa γe γd k y
                                        (bool_decide (k < deqFront))) -∗
  ▷ ([∗ list] k ↦ y ∈ l, cell_resources γtq γa γe γd k y
                                        (bool_decide (k < deqFront + S i))).
Proof.
  iIntros (HFindSome) "HAwaks HR HRRs".
  apply find_index_Some in HFindSome.
  destruct HFindSome as [(v & HEl & HNonSkippable) HRestSkippable].
  rewrite lookup_drop in HEl.
  assert (deqFront + i < length l); first by apply lookup_lt_Some in HEl.
  erewrite <-(take_drop_middle l _ v); last done.
  rewrite !big_sepL_app=>/=.
  iDestruct "HRRs" as "(HInit & H & HTail)".
  apply lookup_lt_Some in HEl. rewrite take_length_le; last lia.
  iSplitL "HInit HAwaks"; last iSplitR "HTail".
  * replace (take _ l) with (take deqFront l ++ take i (drop deqFront l)).
    2: {
      rewrite take_drop_commute.
      replace (take deqFront l) with (take deqFront (take (deqFront + i) l)).
      by rewrite take_drop.
      by rewrite take_take Min.min_l; last lia.
    }
    rewrite !big_sepL_app. iDestruct "HInit" as "[HInit HCancelledCells]".
    iSplitL "HInit".
    { iApply (big_sepL_mono with "HInit"). iIntros (k x HEl') "H".
      assert (k < deqFront)%nat.
      { apply lookup_lt_Some in HEl'.
        by rewrite take_length_le in HEl'; last lia. }
      iEval (rewrite bool_decide_true; last lia).
      rewrite bool_decide_true; last lia. done. }
    { rewrite take_length_le; last lia.
      iAssert (▷ ([∗ list] k ↦ y ∈ take i (drop deqFront l),
              awakening_permit γtq))%I with "[HAwaks]" as "HAwaks".
      { rewrite -big_sepL_replicate.
        rewrite take_length_le //. rewrite drop_length. lia. }
      iCombine "HCancelledCells" "HAwaks" as "HCells".
      rewrite -big_sepL_sep.
      iApply (big_sepL_mono with "HCells"). iIntros (k x HEl') "H".
      assert (k < i)%nat.
      { apply lookup_lt_Some in HEl'. rewrite take_length_le in HEl'=> //.
        rewrite drop_length. lia. }
      rewrite bool_decide_false; last lia.
      rewrite bool_decide_true; last lia.
      rewrite lookup_take in HEl'; last lia.
      specialize (HRestSkippable k).
      destruct HRestSkippable as (y & HEl'' & HSkippable); first lia.
      simplify_eq.
      rewrite /cell_resources.
      rewrite /is_nonskippable in HSkippable.
      destruct x as [[|? ? [[| |[[resolution|]|]]|]]|]=> //.
      iDestruct "H" as "[($ & $ & HRest) HAwak]".
      iDestruct "HRest" as (ℓ) "(H↦ & $ & $ & HRest)".
      iExists ℓ. iFrame "H↦".
      destruct resolution as [[|]|].
      - (* This actually could not have happened: iterator_issued γd could *)
        (* not exist at this point. Thus, we are not "losing" the awakening *)
        (* permit here. *)
        iFrame.
      - iDestruct "HRest" as "($ & $ & [[[H|H] _]|H])";
          [iLeft|iLeft|iRight]; iFrame.
      - iDestruct "HRest" as "($ & $ & [[[H|H] _]|H])";
          [iLeft|iLeft|iRight]; iFrame.
    }
  * rewrite bool_decide_false; last lia.
    rewrite bool_decide_true; last lia.
    rewrite /cell_resources.
    destruct v as [[|? ? [[| |[[|]|]]|]]|]=> //.
    + iDestruct "H" as "($ & $ & H)". iDestruct "H" as (?) "H".
      iExists _. iDestruct "H" as "($ & $ & $ & $ & H)".
      iDestruct "H" as "[[H _]|H]"; [iLeft|iRight]; iFrame; done.
    + iDestruct "H" as "(_ & _ & H)".
      iDestruct "H" as (?) "H".
      iDestruct "H" as "(_ & _ & _ & >HContra & _)".
      iDestruct "HContra" as %[].
    + iDestruct "H" as "($ & $ & H)". iFrame "HR".
      iDestruct "H" as (?) "H". iExists _.
      iDestruct "H" as "($ & $ & $ & $ & _ & [H|H])".
      by iLeft; iFrame.
      by iDestruct "H" as "(>% & _)".
    + iDestruct "H" as "($ & $ & H)". iFrame "HR".
      iDestruct "H" as (?) "H". iExists _.
      by iDestruct "H" as "($ & $ & $ & $ & _ & $)".
    + by iDestruct "H" as "[$ _]".
  * iApply (big_sepL_mono with "HTail"). iIntros (? ? ?) "H".
    rewrite !bool_decide_false; first done; lia.
Qed.

Lemma advance_deqFront_pure i deqFront l:
  find_index is_nonskippable (drop deqFront l) = Some i ->
  deqFront + S i ≤ length l
   ∧ (deqFront + S i > 0
      ∧ (∃ r : option cellState,
           l !! (deqFront + S i - 1) = Some r ∧ is_skippable r) → False).
Proof.
  intros HFindSome.
  apply find_index_Some in HFindSome.
  destruct HFindSome as [(v & HEl & HNonSkippable) HRestSkippable].
  rewrite lookup_drop in HEl.
  assert (deqFront + i < length l); first by apply lookup_lt_Some in HEl.
  split; first lia. case. intros _ (v' & HEl' & HNonSkippable').
  replace (_ - _) with (deqFront + i) in HEl' by lia.
  simplify_eq. rewrite /is_nonskippable in HNonSkippable.
  destruct (is_skippable v); contradiction.
Qed.

Lemma thread_queue_register_for_dequeue γtq γa γe γd l deqFront n:
  ∀ i, find_index is_nonskippable (drop deqFront l) = Some i ->
  ▷ R -∗ ▷ thread_queue_invariant γa γtq γe γd l deqFront -∗
  ▷ thread_queue_state γtq n ==∗
  ▷ (awakening_permit γtq
  ∗ deq_front_at_least γtq (deqFront + S i)
  ∗ thread_queue_invariant γa γtq γe γd l (deqFront + S i)
  ∗ thread_queue_state γtq (n - 1)).
Proof.
  iIntros (i HFindSome) "HR (>H● & HRRs & >HLen & >HDeqIdx) >H◯".
  iDestruct "HLen" as %HLen.
  move: (present_cells_in_take_Si_if_next_present_is_Si _ _ _ HFindSome)
    => HPresentCells.
  assert (find_index is_nonskippable (drop deqFront l) = Some i) as HFindSome';
    first done.
  apply find_index_Some in HFindSome.
  destruct HFindSome as [(v & HEl & HNonSkippable) HRestSkippable].
  rewrite lookup_drop in HEl.
  assert (deqFront + i < length l); first by apply lookup_lt_Some in HEl.
  iMod (deque_register_ra_update with "H● H◯")
    as "($ & HAwaks & H◯ & $)"; first lia.
  simpl. iDestruct "HAwaks" as "[$ HAwaks]".
  rewrite HPresentCells. iFrame "H◯".
  iDestruct (advance_deqFront with "HAwaks HR HRRs") as "$"; first done.
  iPureIntro. by apply advance_deqFront_pure.
Qed.

Theorem thread_queue_register_for_dequeue' E' γtq γa γe γd n e d:
  ↑NTq ⊆ E' ->
  n > 0 ->
  is_thread_queue γa γtq γe γd e d -∗
  ▷ R -∗ ▷ thread_queue_state γtq n ={E'}=∗
  thread_queue_state γtq (n - 1) ∗ awakening_permit γtq.
Proof.
  iIntros (HMask Hn) "[HInv _] HR >HState".
  iInv "HInv" as (l deqFront) "HOpen" "HClose".
  iAssert (▷⌜∃ i, find_index is_nonskippable (drop deqFront l) =
          Some i⌝)%I with "[-]" as "#>HFindIndex".
  { iDestruct "HOpen" as "[>H● _]".
    iDestruct (thread_queue_state_valid with "H● HState") as %->.
    apply count_matching_find_index_Some in Hn. destruct Hn as [i Hn].
    iPureIntro. eauto. }
  iDestruct "HFindIndex" as %[i HFindIndex].
  iMod (thread_queue_register_for_dequeue with "HR HOpen HState")
       as "(>HAwak & _ & HOpen & >HState)"=> //.
  iFrame. iMod ("HClose" with "[HOpen]"); last done.
  by iExists _, _.
Qed.

Lemma awakening_permit_implies_bound γtq l deqFront n:
  own γtq (cell_list_contents_auth_ra l deqFront) -∗
  ([∗] replicate n (awakening_permit γtq)) -∗
  ⌜n <= deqFront⌝.
Proof.
  iIntros "H● HAwaks".
  destruct n; first by iPureIntro; lia.
  rewrite awakening_permit_combine; last lia.
  iDestruct (own_valid_2 with "H● HAwaks")
    as %[[[_ [HValid%nat_included _]%prod_included]%prod_included
             ]%prod_included _]%auth_both_valid.
  simpl in *. iPureIntro; lia.
Qed.

Lemma suspension_permit_implies_bound γtq l deqFront n:
  own γtq (cell_list_contents_auth_ra l deqFront) -∗
  ([∗] replicate n (suspension_permit γtq)) -∗
  ⌜n <= length l⌝.
Proof.
  iIntros "H● HSuspends".
  destruct n; first by iPureIntro; lia.
  rewrite suspension_permit_combine; last lia.
  iDestruct (own_valid_2 with "H● HSuspends")
    as %[[[HValid%nat_included _]%prod_included
             _]%prod_included _]%auth_both_valid.
  simpl in *. iPureIntro; lia.
Qed.

Global Instance is_thread_queue_persistent γa γ γe γd e d:
  Persistent (is_thread_queue γa γ γe γd e d).
Proof. apply _. Qed.

Lemma cell_cancelled_means_skippable γtq γa γe γd i b c:
  cell_cancelled γa i -∗
  cell_resources γtq γa γe γd i (Some c) b -∗
  ⌜if immediateCancellation
   then is_immediately_cancelled (Some c)
   else is_skippable (Some c)⌝.
Proof.
  iIntros "#HCancelled HRR".
  iAssert (cancellation_handle γa i -∗ False)%I with "[]" as "HContra".
  { iIntros "HCancHandle".
    iDestruct (cell_cancellation_handle_not_cancelled with
                   "HCancelled HCancHandle") as %[]. }
  destruct c as [? c'|? ? c']=> /=.
  { iDestruct "HRR" as "(_ & HCancHandle & _)".
    iDestruct ("HContra" with "HCancHandle") as %[]. }
  iDestruct "HRR" as "(_ & _ & HRR)". iDestruct "HRR" as (ℓ) "[_ HRR]".
  destruct c' as [[| |c']|].
  - iDestruct "HRR" as "(_ & _ & _ & HCancHandle & _)".
    iDestruct ("HContra" with "HCancHandle") as %[].
  - iDestruct "HRR" as "(_ & % & _)". iPureIntro. done.
  - iDestruct "HRR" as "(_ & % & HRR)".
    destruct immediateCancellation; first done.
    destruct c' as [c'|].
    2: { iDestruct "HRR" as "[HCancHandle _]".
         iDestruct ("HContra" with "HCancHandle") as %[]. }
    destruct c'; first done.
    iDestruct "HRR" as "(_ & HCancHandle & _)".
    iDestruct ("HContra" with "HCancHandle") as %[].
  - iDestruct "HRR" as "(_ & HCancHandle & _)".
    iDestruct ("HContra" with "HCancHandle") as %[].
Qed.

Lemma cell_cancelled_means_present E' γtq γa γe γd l deqFront ℓ i:
  ↑NArr ⊆ E' ->
  cell_cancelled γa i -∗
  cell_location γtq γa i ℓ -∗
  ▷ thread_queue_invariant γa γtq γe γd l deqFront ={E'}=∗
  ▷ thread_queue_invariant γa γtq γe γd l deqFront ∗
  ▷ ∃ c, ⌜l !! i = Some (Some c) ∧ if immediateCancellation
                                 then is_immediately_cancelled (Some c)
                                 else is_skippable (Some c)⌝.
Proof.
  iIntros (HSets) "#HCanc #H↦ (>H● & HRRs & >%)".
  iMod (acquire_cell _ _ _ _ _ _ with "H↦")
    as "[[#>HCellInit|[>Hℓ HCancHandle]] HCloseCell]"; first done.
  - iMod ("HCloseCell" with "[HCellInit]") as "_"; first by iLeft. iModIntro.
    iDestruct "HCellInit" as "[HCellInit|HCellInit]".
    1: iDestruct "HCellInit" as (? ?) "HCellInit".
    2: iDestruct "HCellInit" as (?) "HCellInit".
    all: iDestruct (rendezvous_state_included' with "H● HCellInit") as
        %(c & HEl & _).
    all: iDestruct (big_sepL_lookup_acc with "HRRs") as "[HRR HRRsRestore]";
      first done.
    all: iDestruct (cell_cancelled_means_skippable with "HCanc HRR")
                   as "#HH".
    all: iSpecialize ("HRRsRestore" with "HRR").
    all: iFrame. all: iSplitR; first by iPureIntro. all: iNext.
    all: iDestruct "HH" as "%"; iPureIntro. all: by eexists.
  - iDestruct (cell_cancellation_handle_not_cancelled with "HCanc HCancHandle")
      as ">[]".
Qed.

(* ENTRY POINTS TO THE CELL ****************************************************)

Lemma deq_front_at_least_from_iterator_issued E' γa γtq γe γd e d i:
  ↑N ⊆ E' ->
  is_thread_queue γa γtq γe γd e d -∗
  iterator_issued γd i ={E'}=∗
  deq_front_at_least γtq (S i) ∗
  iterator_issued γd i.
Proof.
  iIntros (HMask) "(HInv & _ & _ & HD) HIsRes".
  iMod (access_iterator_resources with "HD [#]") as "HH"; first by solve_ndisj.
  by iDestruct (iterator_issued_is_at_least with "HIsRes") as "$".
  rewrite awakening_permit_combine; last lia.
  iDestruct "HH" as "[>HH HHRestore]".
  iInv NTq as (l deqFront) "(>H● & HRRs & HRest)" "HClose".
  rewrite -awakening_permit_combine; last lia.
  iDestruct (awakening_permit_implies_bound with "H● HH") as "#%".
  iMod (cell_list_contents__deq_front_at_least with "H●") as "[H● $]"; first lia.
  iFrame "HIsRes".
  iMod ("HClose" with "[-HH HHRestore]") as "_".
  { iExists _, _. iFrame. }
  by iMod ("HHRestore" with "HH").
Qed.

Lemma inhabit_cell_spec γa γtq γe γd γf i ptr f e d:
  {{{ is_future NFuture V' γf f ∗
      cell_location γtq γa i ptr ∗
      is_thread_queue γa γtq γe γd e d ∗
      future_completion_permit γf 1%Qp ∗
      future_cancellation_permit γf 1%Qp ∗
      iterator_issued γe i }}}
    CAS #ptr (InjLV #()) (InjLV f)
  {{{ (r: bool), RET #r;
      if r
      then rendezvous_thread_handle γtq γf f i
           ∗ future_cancellation_permit γf (1/2)%Qp
      else filled_rendezvous_state γtq i ε
           ∗ iterator_issued γe i
           ∗ future_completion_permit γf 1%Qp
           ∗ future_cancellation_permit γf 1%Qp }}}.
Proof.
  iIntros (Φ) "(#HF & #H↦ & #(HInv & HInfArr & HE & _) & HFCompl & HFCanc & HEnq)
               HΦ".
  wp_bind (CmpXchg _ _ _).
  iMod (access_iterator_resources with "HE [#]") as "HH"; first done.
  by iApply (iterator_issued_is_at_least with "HEnq").
  iDestruct "HH" as "[HH HHRestore]".
  iInv "HInv" as (l' deqFront) "(>H● & HRRs & >HLen & >HDeqIdx)" "HTqClose".
  iDestruct (suspension_permit_implies_bound with "H● HH") as "#>HH'".
  iDestruct "HH'" as %HLength. iSpecialize ("HHRestore" with "HH").
  destruct (lookup_lt_is_Some_2 l' i) as [c HEl]; first lia.
  destruct c as [[? resolution|? ? ?]|].
  - (* A value was already passed. *)
    iMod (own_update with "H●") as "[H● HCellFilled]".
    2: iDestruct ("HΦ" $! false with "[HCellFilled HFCompl HFCanc HEnq]")
      as "HΦ"; first by iFrame; iExists _.
    { apply auth_update_core_id. by apply _.
      apply prod_included; split=>/=; first by apply ucmra_unit_least.
      apply prod_included; split=>/=; last by apply ucmra_unit_least.
      apply list_singletonM_included. eexists. rewrite map_lookup HEl /=.
      split; first done. apply Some_included. right. apply Cinl_included.
      apply prod_included. split=>/=; first done. apply ucmra_unit_least.
    }
    iDestruct (big_sepL_lookup_acc with "HRRs") as "[HRR HRRsRestore]";
      first done.
    simpl.
    iDestruct "HRR" as "(H1 & H2 & H3 & HRR)".
    iDestruct "HRR" as (ℓ) "[H↦' HRR]".
    iDestruct (infinite_array_mapsto_agree with "H↦ H↦'") as "><-".
    destruct resolution as [[|]|].
    iDestruct "HRR" as "[HRR|HRR]".
    all: iDestruct "HRR" as "(Hℓ & HRR)"; wp_cmpxchg_fail.
    all: iDestruct ("HRRsRestore" with "[H1 H2 H3 HRR Hℓ]") as "HRRs";
      first by (eauto 10 with iFrame).
    all: iMod ("HTqClose" with "[-HΦ HHRestore]") as "_";
      first by iExists _, _; iFrame.
    all: by iModIntro; iMod "HHRestore"; iModIntro; wp_pures.
  - (* Cell already inhabited? Impossible. *)
    iDestruct (big_sepL_lookup with "HRRs") as "HRR"; first done.
    iDestruct "HRR" as "[>HEnq' _]".
    iDestruct (iterator_issued_exclusive with "HEnq HEnq'") as %[].
  - iMod (acquire_cell _ _ _ _ _ _ with "H↦")
      as "[[#>HCellInit|[>Hℓ HCancHandle]] HCloseCell]";
      first by solve_ndisj.
    { (* We know the rendezvous is not yet initialized. *)
      iAssert (∃ s, rendezvous_state γtq i (Some s))%I with "[]"
        as (?) "HContra".
      { iDestruct "HCellInit" as "[H|H]".
        iDestruct "H" as (? ?) "H"; iExists _; iFrame "H".
        iDestruct "H" as (?) "H"; iExists _; iFrame "H". }
      iDestruct (rendezvous_state_included with "H● HContra")
        as %(c & HEl' & HInc).
      simplify_eq. simpl in HInc. by apply included_None in HInc.
    }
    wp_cmpxchg_suc.
    iMod (inhabit_cell_ra with "H●") as "(H● & #HLoc)"; first done.
    iEval (rewrite -Qp_half_half) in "HFCanc".
    rewrite future_cancellation_permit_Fractional.
    iDestruct "HFCanc" as "[HFHalfCanc1 HFHalfCanc2]".
    iMod ("HCloseCell" with "[]") as "_"; last iModIntro.
    { iLeft. iNext. iLeft. iExists _, _. iApply "HLoc". }
    iSpecialize ("HΦ" $! true with "[$]").
    iMod ("HTqClose" with "[-HΦ HHRestore]").
    2: by iModIntro; iMod "HHRestore"; iModIntro; wp_pures.
    iExists _, _. iFrame "H●". rewrite insert_length. iFrame "HLen".
    iSplitR "HDeqIdx".
    2: {
      iDestruct "HDeqIdx" as %HDeqIdx. iPureIntro.
      case. intros ? (r & HEl' & HSkippable). apply HDeqIdx. split; first done.
      destruct (decide (i = deqFront - 1)).
      - subst. rewrite list_insert_alter list_lookup_alter HEl in HEl'.
        simpl in *. simplify_eq. contradiction.
      - rewrite list_lookup_insert_ne in HEl'; last lia.
        eexists. done.
    }
    iDestruct (big_sepL_insert_acc with "HRRs") as "[HPre HRRsRestore]";
      first done.
    iApply "HRRsRestore". simpl. iFrame "HEnq HLoc HF".
    iExists _. iFrame "H↦ Hℓ HCancHandle". iDestruct "HPre" as "[$ $]".
    iFrame.
Qed.

Lemma pass_value_to_empty_cell_spec
      (synchronously: bool) γtq γa γe γd i ptr e d v:
  lit_is_unboxed v ->
  {{{ is_thread_queue γa γtq γe γd e d ∗
      deq_front_at_least γtq (S i) ∗
      cell_location γtq γa i ptr ∗
      iterator_issued γd i ∗
      V v }}}
    CAS #ptr (InjLV #()) (InjRV #v)
  {{{ (r: bool), RET #r;
      if r
      then if synchronously
           then cell_breaking_token γtq i ∗ rendezvous_filled_value γtq #v i
           else E
      else inhabited_rendezvous_state γtq i ε ∗ iterator_issued γd i ∗ V v
  }}}.
Proof.
  iIntros (HValUnboxed Φ) "(#HTq & #HDeqFront & #H↦ & HIsRes & Hv) HΦ".
  wp_bind (CmpXchg _ _ _).
  iDestruct "HTq" as "(HInv & HInfArr & _ & _)".
  iInv "HInv" as (l deqFront) "(>H● & HRRs & >HLen & >HDeqIdx)" "HTqClose".
  iDestruct "HLen" as %HLen.
  iDestruct (deq_front_at_least_valid with "H● HDeqFront") as %HDeqFront.
  assert (i < length l) as HLt; first lia.
  apply lookup_lt_is_Some in HLt. destruct HLt as [c HEl].
  iDestruct (big_sepL_insert_acc with "HRRs") as "[HRR HRRsRestore]"; first done.
  destruct c as [[r|γf f r]|].
  - (* The cell could not have been already filled. *)
    iDestruct "HRR" as "[HIsRes' _]".
    iDestruct (iterator_issued_exclusive with "HIsRes HIsRes'") as ">[]".
  - (* CAS fails, as the suspender already arrived. *)
    iAssert (▷ ∃ v, ⌜v ≠ InjLV #()⌝
                    ∗ ptr ↦ v
                    ∗ (ptr ↦ v -∗ cell_resources γtq γa γe γd i
                           (Some (cellInhabited γf f r))
                           (bool_decide (i < deqFront))))%I
            with "[HRR]" as (inh) "(>% & Hℓ & HRRRestore)".
    {
      simpl. iDestruct "HRR" as "($ & [#HIsFuture $] & HRR)".
      iAssert (▷ ⌜InjLV f ≠ InjLV #()⌝)%I as ">%".
      { iDestruct (future_is_not_unit with "HIsFuture") as ">%".
        iPureIntro. case. intros ->. contradiction. }
      iFrame "HIsFuture".
      iDestruct "HRR" as (ptr') "[H↦' HRR]".
      iDestruct (infinite_array_mapsto_agree with "H↦ H↦'") as "><-".
      destruct r as [[ | |r]|].
      4: iDestruct "HRR" as "[Hℓ $]".
      3: {
        iDestruct "HRR" as "($ & $ & HRR)".
        destruct r as [[[[|]|]|]|];
          try by iDestruct "HRR" as "[Hℓ HRR]";
          iExists _; iFrame "Hℓ"; iSplitR; first (by iPureIntro);
          iNext; iIntros "Hℓ"; iExists _; by iFrame.
        - iDestruct "HRR" as "(HRR & $ & $)".
          iDestruct "HRR" as "[[Hℓ HRR]|[Hℓ HRR]]".
          all: iExists _; iFrame "Hℓ"; iSplitR; first by iPureIntro.
          all: iNext; iIntros "Hℓ"; iExists _; iFrame "H↦".
          by iLeft; iFrame.
          by iRight; iFrame.
        - iDestruct "HRR" as "($ & $ & HRR)".
          iDestruct "HRR" as "[[Hℓ HRR]|[[Hℓ HRR]|HRR]]".
          + iExists _; iFrame "Hℓ"; iSplitR; first (by iPureIntro).
            iNext; iIntros "Hℓ"; iExists _. iFrame "H↦". iLeft. iFrame.
          + iExists _; iFrame "Hℓ"; iSplitR; first (by iPureIntro).
            iNext; iIntros "Hℓ"; iExists _. iFrame "H↦". iRight. iLeft. iFrame.
          + iDestruct "HRR" as (?) "(HUnboxed & Hℓ & HRR)".
            iExists _; iFrame "Hℓ"; iSplitR; first (by iPureIntro).
            iNext; iIntros "Hℓ"; iExists _. iFrame "H↦". iRight. iRight.
            iExists _. iFrame.
        - iDestruct "HRR" as "($ & HR' & HRR)".
          iDestruct "HRR" as "[[Hℓ HR]|[>% HR]]".
          + iExists _; iFrame "Hℓ"; iSplitR; first (by iPureIntro).
            iNext; iIntros "Hℓ"; iExists _. iFrame "H↦ HR'". iLeft. iFrame.
          + iDestruct "HR" as (?) "(HUnboxed & Hℓ & HR)".
            iExists _; iFrame "Hℓ"; iSplitR; first (by iPureIntro).
            iNext; iIntros "Hℓ"; iExists _. iFrame "H↦ HR'". iRight.
            iSplitR; first by iPureIntro. iExists _. iFrame.
      }
      2: iDestruct "HRR" as "[[Hℓ|Hℓ] $]".
      1: iDestruct "HRR" as "[[Hℓ|Hℓ] $]".
      all: iExists _; iFrame "Hℓ"; iSplitR; first by iPureIntro.
      all: iNext; iIntros "Hℓ"; iExists _; by iFrame.
    }
    wp_cmpxchg_fail.
    iDestruct ("HRRRestore" with "Hℓ") as "HRR".
    iDestruct ("HRRsRestore" with "HRR") as "HRRs".
    iMod (own_update with "H●") as "[H● H◯]".
    2: iSpecialize ("HΦ" $! false with "[H◯ HIsRes Hv]");
      first by iFrame; iExists _, _.
    {
      apply auth_update_core_id. by apply _.
      apply prod_included=>/=. split; first by apply ucmra_unit_least.
      apply prod_included=>/=. split; last by apply ucmra_unit_least.
      apply list_singletonM_included. eexists.
      rewrite map_lookup HEl=>/=. split; first done.
      rewrite Some_included. right. apply Cinr_included.
      apply prod_included=>/=. split; last by apply ucmra_unit_least.
      done.
    }
    iMod ("HTqClose" with "[-HΦ]") as "_"; last by iModIntro; wp_pures.
    rewrite list_insert_id; last done.
    iExists _, _. iFrame. iPureIntro; lia.
  - iMod (acquire_cell _ _ _ _ _ _ with "H↦")
      as "[[#>HCellInit|[>Hℓ HCancHandle]] HCloseCell]";
      first by solve_ndisj.
    { (* We know the rendezvous is not yet initialized. *)
      iAssert (∃ s, rendezvous_state γtq i (Some s))%I with "[]"
        as (?) "HContra".
      { iDestruct "HCellInit" as "[H|H]".
        iDestruct "H" as (? ?) "H"; iExists _; iFrame "H".
        iDestruct "H" as (?) "H"; iExists _; iFrame "H". }
      iDestruct (rendezvous_state_included with "H● HContra")
        as %(c & HEl' & HInc).
      simplify_eq. simpl in HInc. by apply included_None in HInc.
    }
    wp_cmpxchg_suc.
    iDestruct "HRR" as "[HE HR]". rewrite bool_decide_true; last lia.
    iMod (fill_cell_ra with "H●") as "(H● & #HInitialized & HCB)"; first done.
    iMod ("HCloseCell" with "[]") as "_"; last iModIntro.
    { iLeft. iRight. iExists _. done. }
    iSpecialize ("HΦ" $! true). destruct synchronously.
    + iSpecialize ("HΦ" with "[HCB]"); first by iFrame.
      iMod ("HTqClose" with "[-HΦ]"); last by iModIntro; wp_pures.
      iExists _, _. iFrame "H●". rewrite insert_length.
      iDestruct "HDeqIdx" as %HDeqIdx. iSplitL.
      2: {
        iPureIntro; split; first lia.
        case. intros ? (r & HEl' & HSkippable). apply HDeqIdx. split; first done.
        destruct (decide (i = deqFront - 1)).
        - subst. rewrite list_insert_alter list_lookup_alter HEl in HEl'.
          simpl in *. simplify_eq. contradiction.
        - rewrite list_lookup_insert_ne in HEl'; last lia.
        eexists. done.
      }
      iApply "HRRsRestore". simpl. iFrame. iSplitR; first done.
      iExists _. by iFrame.
    + iSpecialize ("HΦ" with "HE").
      iMod (take_cell_value_ra with "H●") as "[H● #H◯]".
      { erewrite list_lookup_insert=> //. lia. }
      rewrite list_insert_insert.
      iMod ("HTqClose" with "[-HΦ]"); last by iModIntro; wp_pures.
      iExists _, _. iFrame "H●". rewrite insert_length.
      iDestruct "HDeqIdx" as %HDeqIdx. iSplitL.
      2: {
        iPureIntro; split; first lia.
        case. intros ? (r & HEl' & HSkippable). apply HDeqIdx. split; first done.
        destruct (decide (i = deqFront - 1)).
        - subst. rewrite list_insert_alter list_lookup_alter HEl in HEl'.
          simpl in *. simplify_eq. contradiction.
        - rewrite list_lookup_insert_ne in HEl'; last lia.
        eexists. done.
      }
      iApply "HRRsRestore". simpl. iFrame. iSplitR; first done.
      iExists _. iFrame "H↦".
      iLeft. iFrame.
Qed.

Lemma deq_front_at_least_from_auth_ra γtq l deqFront:
  own γtq (cell_list_contents_auth_ra l deqFront) ==∗
  own γtq (cell_list_contents_auth_ra l deqFront) ∗
  deq_front_at_least γtq deqFront.
Proof.
  iIntros "H●". iMod (own_update with "H●") as "[$ $]"; last done.
  apply auth_update_core_id. by apply _.
  apply prod_included=> /=. split; last by apply ucmra_unit_least.
  apply prod_included=> /=. split; first by apply ucmra_unit_least.
  apply prod_included=> /=. split; first by apply ucmra_unit_least.
  done.
Qed.

Theorem dequeue_iterator_update γa γtq γe γd e d:
  ⊢ is_thread_queue γa γtq γe γd e d -∗
    ⌜¬ immediateCancellation⌝ -∗
    make_laterable (∀ l start finish,
      (∀ i, ⌜start ≤ i < finish⌝ -∗ cell_cancelled γa i ∗
                                    (∃ ℓ, cell_location γtq γa i ℓ)) -∗
      ▷ [∗] replicate (S start) (awakening_permit γtq) -∗
      ([∗ list] i ∈ l, ⌜start ≤ i < finish⌝ ∗ iterator_issued γd i)
      ={⊤ ∖ ↑NDeq}=∗ ▷ [∗] replicate ((S start) + length l) (awakening_permit γtq)).
Proof.
  iIntros "(#HInv & _ & _ & _)" (HCanc).
  iApply (make_laterable_intro True%I); last done.
  iModIntro. iIntros "_" (cancelledCells start finish) "#HCancelled".
  iIntros "HPermits HCells".
  rewrite replicate_plus big_sepL_app.
  iInv "HInv" as (l deqFront) "HOpen" "HClose".
  iDestruct "HOpen" as "(>H● & HRRs & HLen & >HDeqFront)".
  iDestruct "HDeqFront" as %HDeqFront.
  iMod (deq_front_at_least_from_auth_ra with "H●") as "[H● #HDeqFront]".
  iDestruct (awakening_permit_implies_bound with "H● HPermits")
    as "#>HDeqFront'".
  iDestruct "HDeqFront'" as %HDeqFront'.
  iFrame "HPermits".
  iAssert (|={⊤ ∖ ↑NDeq ∖ ↑NTq}=>
           ▷ thread_queue_invariant γa γtq γe γd l deqFront ∗
            [∗ list] i ∈ seq start (finish - start - 1),
           ⌜∃ c, l !! i = Some c ∧ is_skippable c⌝)%I
          with "[H● HRRs HLen]" as ">[HTq HSkippable]".
  { remember (finish - start) as r.
    iAssert (▷ thread_queue_invariant γa γtq γe γd l deqFront)%I
      with "[H● HRRs HLen]" as "HTq". by iFrame.
    clear HDeqFront'.
    iInduction r as [|r'] "IH" forall (start Heqr) "HCancelled".
    - simpl. iFrame. by iPureIntro.
    - simpl. destruct r' as [|r''].
      by simpl; iFrame.
      iDestruct ("HCancelled" $! start with "[%]") as "[HCellCancelled H↦]".
      by lia.
      iDestruct "H↦" as (ℓ) "H↦".
      iMod (cell_cancelled_means_present with "HCellCancelled H↦ HTq")
           as "[HH >HH']". by solve_ndisj.
      destruct immediateCancellation. done.
      iDestruct "HH'" as %(c & HEl & HSkippable). simpl.
      iAssert (⌜∃ c, l !! start = Some c ∧ is_skippable c⌝)%I
              with "[%]" as "$"; first by eexists.
      rewrite !Nat.sub_0_r.
      iApply ("IH" $! (S start) with "[%] HH [HCancelled]"). lia.
      iIntros "!>" (i HEl'). iApply "HCancelled". iPureIntro. lia. }
  rewrite big_sepL_forall. iDestruct "HSkippable" as %HSkippable.
  assert (finish ≤ deqFront).
  {
    destruct (decide (finish ≤ deqFront)); first lia. exfalso.
    case HDeqFront. split; first lia.
    eapply (HSkippable (deqFront - start - 1)). apply lookup_seq.
    split; lia.
  }
  iMod ("HClose" with "[HTq]") as "_"; first by iExists _, _; iFrame.
  rewrite big_sepL_replicate big_sepL_later -big_sepL_fupd.
  iApply (big_sepL_impl with "HCells").
  iIntros "!>" (k i _) "[HBounds HIsRes]". iDestruct "HBounds" as %[HB1 HB2].
  iDestruct ("HCancelled" $! i with "[%]") as "[#HCellCanc H↦]"; first lia.
  iDestruct "H↦" as (ℓ) "H↦".
  iInv "HInv" as (l' deqFront') "HOpen" "HClose".
  iMod (cell_cancelled_means_present with "HCellCanc H↦ HOpen")
        as "[HOpen >HFact]".
  by solve_ndisj. iDestruct "HFact" as %(c & HEl & HFact).
  iDestruct "HOpen" as "(>H● & HRRs & HRest)".
  iDestruct (big_sepL_lookup_acc with "HRRs") as "[HRR HRRsRestore]";
    first done.
  destruct immediateCancellation; first done. simpl in *.
  destruct c as [|? ? [[| |[[c'|]|]]|]]=>//.
  iDestruct "HRR" as "(HIsSus & HTh & HRR)".
  iDestruct "HRR" as (ℓ') "(H↦' & HFutureCancelled & HNotCanc & HRR)".
  iDestruct (deq_front_at_least_valid with "H● HDeqFront") as %HDeqFront''.
  assert (i < deqFront') by lia.
  rewrite bool_decide_true; last lia.
  destruct c' as [[|]|].
  3: iDestruct "HRR" as "(Hℓ & HE & [[[HFC|[_ HC]] >$]|[_ HC]])".
  2: iDestruct "HRR" as "(Hℓ & HTok & [[[HFC|[_ HC]] >$]|[_ HC]])".
  1: iDestruct "HRR" as "(_ & HC & _)".
  all: try by iDestruct (iterator_issued_exclusive with "HIsRes HC") as ">[]".
  all: iMod ("HClose" with "[-]"); last done.
  all: iExists _, _; iFrame; iApply "HRRsRestore".
  all: iFrame. all: iExists _. all: by iFrame.
Qed.

Lemma read_cell_value_by_resumer_spec γtq γa γe γd i ptr e d:
  {{{ deq_front_at_least γtq (S i) ∗
      is_thread_queue γa γtq γe γd e d ∗
      cell_location γtq γa i ptr ∗
      iterator_issued γd i }}}
    !#ptr
  {{{ (v: val), RET v;
      (⌜v = NONEV⌝ ∧ iterator_issued γd i ∨
       ⌜v = CANCELLEDV⌝ ∧ (if immediateCancellation then R
                           else awakening_permit γtq) ∨
       ⌜v = REFUSEDV⌝ ∧ ERefuse ∨
       ∃ γf f, ⌜v = InjLV f⌝ ∧ rendezvous_thread_handle γtq γf f i ∗
               future_completion_permit γf (1/2)%Qp)
  }}}.
Proof.
  iIntros (Φ) "(#HDeqFront & #(HInv & HInfArr & _ & HD) & #H↦ & HIsRes) HΦ".
  iMod (access_iterator_resources with "HD [#]") as "HH"; first done.
  { iApply (own_mono with "HIsRes"). apply auth_included; split=>//=.
    apply prod_included; split; first by apply ucmra_unit_least.
    apply max_nat_included. simpl. done. }
  iDestruct "HH" as "[HH HHRestore]".
  iMod (acquire_cell _ _ _ _ _ _ with "H↦")
    as "[[#>HCellInit|[>Hℓ HCancHandle]] HCloseCell]"; first by solve_ndisj.
  2: { (* Cell was not yet inhabited, so NONEV is written in it. *)
    wp_load. iMod ("HCloseCell" with "[Hℓ HCancHandle]") as "_".
    by iRight; iFrame. iModIntro. iMod ("HHRestore" with "HH").
    iApply "HΦ". by iLeft; iFrame.
  }
  iSpecialize ("HCloseCell" with "[HCellInit]"); first by iLeft.
  iInv "HInv" as (l deqFront) "(>H● & HRRs & >HLen & >HDeqIdx)" "HTqClose".
  iDestruct (awakening_permit_implies_bound with "H● HH") as "#>HValid".
  iDestruct "HValid" as %HValid.
  iSpecialize ("HHRestore" with "[HH]"); first done.
  iDestruct "HCellInit" as "[HCellInhabited|HCellFilled]".
  2: { (* Cell could not have been filled already, we hold the permit. *)
    iDestruct "HCellFilled" as (?) "HCellFilled".
    iDestruct (rendezvous_state_included' with "H● HCellFilled")
      as %(c & HEl & HInc).
    destruct c as [? c'|].
    2: { exfalso. simpl in *. move: HInc. rewrite csum_included.
        case; first done. case; by intros (? & ? & ? & ? & ?). }
    iDestruct (big_sepL_lookup with "HRRs") as "HRR"; first done.
    iDestruct "HRR" as "[>HContra _]".
    iDestruct (iterator_issued_exclusive with "HContra HIsRes") as %[].
  }
  (* Cell was inhabited. *)
  iDestruct "HCellInhabited" as (? ?) "HCellInhabited".
  iDestruct (rendezvous_state_included' with "H● HCellInhabited")
    as %(c & HEl & HInc).
  destruct c as [? c'|? ? c'].
  1: { exfalso. simpl in *. move: HInc. rewrite csum_included.
        case; first done. case; by intros (? & ? & ? & ? & ?). }
  move: HInc; rewrite Cinr_included pair_included to_agree_included.
  case. case=> /= HEq1 HEq2 _. simplify_eq.
  iDestruct (big_sepL_lookup_acc with "HRRs") as "[HRR HRRsRestore]";
    first done.
  iDestruct (deq_front_at_least_valid with "H● HDeqFront") as %HDeqFront.
  rewrite bool_decide_true; last lia.
  iDestruct "HRR" as "(HIsSus & #HTh & HRR)". iDestruct "HRR" as (ℓ) "[H↦' HRR]".
  iDestruct (infinite_array_mapsto_agree with "H↦ H↦'") as "><-".
  destruct c' as [[| |c'']|].
  - (* Cell could not have been resumed already. *)
    iDestruct "HRR" as "(_ & >HContra & _)".
    iDestruct (iterator_issued_exclusive with "HContra HIsRes") as %[].
  - iDestruct "HRR" as
        "(Hℓ & >HImmediate & HCancelled & [HCompletion|[_ HC]])".
    iDestruct "HImmediate" as %HImmediate.
    iDestruct "HCompletion" as "[[HCompletionPermit|[_ HC]] HR]".
    all: try by iDestruct (iterator_issued_exclusive with "HIsRes HC") as ">[]".
    iDestruct "Hℓ" as "[Hℓ|Hℓ]"; wp_load.
    + iEval (rewrite -Qp_half_half future_completion_permit_Fractional)
        in "HCompletionPermit".
      iDestruct "HCompletionPermit" as "[HCompl1 HCompl2]".
      iSpecialize ("HΦ" $! (InjLV _) with "[HCompl2]").
      { repeat iRight. iExists _, _. iFrame. iSplit; last by iAssumption. done. }
      iMod ("HTqClose" with "[-HCloseCell HHRestore HΦ]").
      2: iModIntro; iMod "HCloseCell"; iModIntro; by iMod "HHRestore".
      iExists _, _. iFrame "H● HDeqIdx HLen". iApply "HRRsRestore".
      iFrame "HIsSus HTh HCancelled". iExists _. iFrame "H↦".
      iSplitL "Hℓ"; first by iLeft. iSplitR; first done. iLeft. iFrame.
      iRight; iFrame.
    + iSpecialize ("HΦ" $! CANCELLEDV with "[HR]").
      { iRight. iLeft. destruct immediateCancellation=> //. by iFrame. }
      iMod ("HTqClose" with "[-HCloseCell HHRestore HΦ]").
      2: iModIntro; iMod "HCloseCell"; iModIntro; by iMod "HHRestore".
      iExists _, _. iFrame "H● HDeqIdx HLen". iApply "HRRsRestore".
      iFrame "HIsSus HTh HCancelled". iExists _. iFrame "H↦".
      iSplitL "Hℓ"; first by iRight. iSplitR; first done. iRight. iFrame.
  - iDestruct "HRR" as "(HCancelled & >HNotImmediate & HRR)".
    iDestruct "HNotImmediate" as %HNotImmediate.
    destruct c'' as [[[[|]|]|]|].
    + (* Value couldn't have been taken, as it hasn't been passed. *)
      iDestruct "HRR" as "(_ & HC & _)".
      by iDestruct (iterator_issued_exclusive with "HIsRes HC") as ">[]".
    + (* The cell was cancelled successfully. *)
      iDestruct "HRR" as "(Hℓ & HTok & [[[HFutureCompl|[_ HC]] HAwak]|[_ HC]])".
      all: try by iDestruct (iterator_issued_exclusive with "HIsRes HC")
          as ">[]".
      wp_load.
      iSpecialize ("HΦ" $! CANCELLEDV with "[HAwak]").
      { iRight. iLeft. iSplitR; first done. by destruct immediateCancellation. }
      iMod ("HTqClose" with "[-HCloseCell HHRestore HΦ]").
      2: iModIntro; iMod "HCloseCell"; iModIntro; by iMod "HHRestore".
      iExists _, _. iFrame "H● HDeqIdx HLen". iApply "HRRsRestore".
      iFrame "HIsSus HTh HCancelled". iExists _. iFrame "H↦ Hℓ HTok".
      iSplitR; first done. iRight. iFrame.
    + (* The cell is attempting to cancel. *)
      iDestruct "HRR" as "(Hℓ & HE & [[[HFutureCompl|[_ HC]] HAwak]|[_ HC]])".
      all: try by iDestruct (iterator_issued_exclusive with "HIsRes HC")
          as ">[]".
      iEval (rewrite -Qp_half_half future_completion_permit_Fractional)
        in "HFutureCompl".
      iDestruct "HFutureCompl" as "[HCompl1 HCompl2]".
      wp_load.
      iSpecialize ("HΦ" $! (InjLV _) with "[HCompl2]").
      { repeat iRight. iExists _, _. iFrame. iSplit=>//. }
      iMod ("HTqClose" with "[-HCloseCell HHRestore HΦ]").
      2: iModIntro; iMod "HCloseCell"; iModIntro; by iMod "HHRestore".
      iExists _, _. iFrame "H● HDeqIdx HLen". iApply "HRRsRestore".
      iFrame "HIsSus HTh HCancelled". iExists _. iFrame "H↦ Hℓ HE".
      iSplitR; first done. iLeft. iFrame. iRight; iFrame.
    + (* Cancellation was prevented. *)
      iDestruct "HRR" as "(HInside & HCancHandle & HRR)".
      iDestruct "HRR" as "[(Hℓ & HE & [HFutureCompl|[_ HC]])|
        [(Hℓ & [[[HFutureCompl|[_ HC]] HE]|[_ HC]] & HCancTok)|HRR]]";
        last iDestruct "HRR" as (?) "(_ & _ & HC & _)".
      all: try by iDestruct (iterator_issued_exclusive with "HIsRes HC")
          as ">[]".
      all: wp_load.
      { iEval (rewrite -Qp_half_half future_completion_permit_Fractional)
          in "HFutureCompl".
        iDestruct "HFutureCompl" as "[HCompl1 HCompl2]".
        iSpecialize ("HΦ" $! (InjLV _) with "[HCompl2]").
        { repeat iRight. iExists _, _. iFrame. iSplit=>//. }
        iMod ("HTqClose" with "[-HCloseCell HHRestore HΦ]").
        2: iModIntro; iMod "HCloseCell"; iModIntro; by iMod "HHRestore".
        iExists _, _. iFrame "H● HDeqIdx HLen". iApply "HRRsRestore".
        iFrame "HInside HIsSus HTh HCancelled HCancHandle". iExists _.
        iFrame "H↦". iSplitR; first done. iLeft. iFrame. iRight. iFrame. }
      { iSpecialize ("HΦ" $! REFUSEDV with "[HE]").
        { iRight. iRight. iLeft. by iFrame. }
        iMod ("HTqClose" with "[-HCloseCell HHRestore HΦ]").
        2: iModIntro; iMod "HCloseCell"; iModIntro; by iMod "HHRestore".
        iExists _, _. iFrame "H● HDeqIdx HLen". iApply "HRRsRestore".
        iFrame "HInside HIsSus HTh HCancelled HCancHandle". iExists _.
        iFrame "H↦". iSplitR; first done. iRight. iLeft. iFrame. }
    + (* Cell was cancelled, but this fact was not registered. *)
      iDestruct "HRR" as "(HCancHandle & HR' &
        [(Hℓ & HE & [HFutureCompl|[_ HC]])|(_ & HRR)])";
        last iDestruct "HRR" as (?) "(_ & _ & HC & _)".
      all: try by iDestruct (iterator_issued_exclusive with "HIsRes HC")
          as ">[]".
      iEval (rewrite -Qp_half_half future_completion_permit_Fractional)
        in "HFutureCompl".
      iDestruct "HFutureCompl" as "[HCompl1 HCompl2]".
      wp_load.
      iSpecialize ("HΦ" $! (InjLV _) with "[HCompl2]").
      { repeat iRight. iExists _, _. iFrame. iSplit=>//. }
      iMod ("HTqClose" with "[-HCloseCell HHRestore HΦ]").
      2: iModIntro; iMod "HCloseCell"; iModIntro; by iMod "HHRestore".
      iExists _, _. iFrame "H● HDeqIdx HLen". iApply "HRRsRestore".
      iFrame "HCancHandle HIsSus HTh". iExists _. iFrame "H↦ HCancelled".
      iSplitR; first done. iFrame "HR'". iLeft. iFrame. iRight. iFrame.
  - iDestruct "HRR" as "(Hℓ & HCancHandle & HE & HR & HFutureCanc &
      [HFutureCompl|[_ HC]])".
    2: by iDestruct (iterator_issued_exclusive with "HIsRes HC") as ">[]".
    iEval (rewrite -Qp_half_half future_completion_permit_Fractional)
      in "HFutureCompl".
    iDestruct "HFutureCompl" as "[HCompl1 HCompl2]".
    wp_load.
    iSpecialize ("HΦ" $! (InjLV _) with "[HCompl2]").
    { repeat iRight. iExists _, _. iFrame. iSplit=>//. }
    iMod ("HTqClose" with "[-HCloseCell HHRestore HΦ]").
    2: iModIntro; iMod "HCloseCell"; iModIntro; by iMod "HHRestore".
    iExists _, _. iFrame "H● HDeqIdx HLen". iApply "HRRsRestore".
    iFrame "HCancHandle HIsSus HTh". iExists _. iFrame "H↦". iFrame.
    iRight. iFrame.
Qed.

Lemma acquire_resumer_resource_from_immediately_cancelled E' γtq γa γe γd i e d ℓ:
  (↑NTq ∪ ↑NArr) ⊆ E' ->
  immediateCancellation ->
  is_thread_queue γa γtq γe γd e d -∗
  deq_front_at_least γtq (S i) -∗
  cell_cancelled γa i -∗
  cell_location γtq γa i ℓ -∗
  iterator_issued γd i ={E'}=∗
  ▷ R.
Proof.
  iIntros (HMask HImmediate) "[#HInv _] #HDeqFront #HCancelled #H↦ HIsRes".
  iInv "HInv" as (l deqFront) "HTq" "HClose".
  iMod (cell_cancelled_means_present with "HCancelled H↦ HTq") as
      "[HTq >HSkippable]"; first by solve_ndisj.
  iDestruct "HSkippable" as %(c & HEl & HCancelled).
  destruct immediateCancellation; last done. simpl in HCancelled.
  destruct c as [|? ? [[| |]|]]=> //.
  iDestruct "HTq" as "(>H● & HRRs & HRest)".
  iDestruct (big_sepL_lookup_acc with "HRRs") as "[HRR HRRs]"; first done.
  iDestruct (deq_front_at_least_valid with "H● HDeqFront") as %HDeqFront.
  rewrite bool_decide_true; last lia.
  simpl. iDestruct "HRR" as "(HIsSus & HTh & HRR)".
  iDestruct "HRR" as (ℓ') "(H↦' & Hℓ & HImmediate & HFutureCancelled & HRR)".
  iDestruct "HRR" as "[[[HFuture|[_ >HC]] HR]|[_ >HC]]".
  all: try by iDestruct (iterator_issued_exclusive with "HC HIsRes") as %[].
  iFrame "HR".
  iMod ("HClose" with "[-]"); last done. iExists _, _. iFrame "H● HRest".
  iApply "HRRs". iFrame "HIsSus HTh". iExists _. by iFrame.
Qed.

(* TRANSITIONS ON CELLS IN THE NON-SUSPENDING CASE *****************************)

Lemma check_passed_value (suspender_side: bool) γtq γa γe γd i (ptr: loc) vf:
  rendezvous_filled_value γtq vf i -∗
  cell_location γtq γa i ptr -∗
  (if suspender_side then iterator_issued γe i else cell_breaking_token γtq i) -∗
  <<< ∀ l deqFront, ▷ thread_queue_invariant γa γtq γe γd l deqFront >>>
    !#ptr @ ⊤
  <<< ∃ v, thread_queue_invariant γa γtq γe γd l deqFront ∗
           match l !! i with
           | Some (Some (cellPassedValue _ d)) =>
             match d with
               | None => ⌜v = InjRV vf⌝ ∧
                        (if suspender_side then iterator_issued γe i
                         else cell_breaking_token γtq i)
               | Some cellBroken => ⌜v = BROKENV ∧ suspender_side⌝ ∗
                                   E ∗ CB
               | Some cellRendezvousSucceeded =>
                 if suspender_side then ⌜v = InjRV vf⌝ ∧ iterator_issued γe i
                 else ⌜v = TAKENV⌝ ∧ E
             end
           | _ => False
           end, RET v >>>.
Proof.
  iIntros "#HFilled #H↦ HCellBreaking" (Φ) "AU".
  iMod "AU" as (l deqFront) "[(>H● & HRRs & >HLen & >HDeqIdx) [_ HClose]]".
  iDestruct (rendezvous_state_included' with "H● HFilled") as %(c & HEl & HInc).
  rewrite HEl. destruct c as [? c'|].
  2: { exfalso. simpl in *. move: HInc. rewrite csum_included.
       case; first done. case; by intros (? & ? & ? & ? & ?). }
  move: HInc. rewrite Cinl_included pair_included to_agree_included. case=> HEq _.
  simplify_eq.
  iDestruct (big_sepL_lookup_acc with "HRRs") as "[HRR HRRsRestore]";
    first done.
  simpl. iDestruct "HRR" as "(HIsRes & HCancHandle & HValUnboxed & HRR)".
  iDestruct "HRR" as (ℓ) "[H↦' HRR]".
  iDestruct (infinite_array_mapsto_agree with "H↦ H↦'") as "><-".
  destruct c' as [[|]|]=> /=.
  - iDestruct "HRR" as "[(Hptr & HCellBreaking' & HRR)|(Hptr & HRR)]"; wp_load.
    all: iMod ("HClose" with "[-]") as "HΦ"; last by iModIntro.
    * destruct suspender_side.
      + iSplitR "HCellBreaking".
        { iFrame "H● HLen HDeqIdx". iApply "HRRsRestore".
          iFrame "HIsRes HCancHandle HValUnboxed".
          iExists _. iFrame "H↦". iLeft. iFrame. }
        by iFrame; iPureIntro.
      + iDestruct (cell_breaking_token_exclusive
                     with "HCellBreaking HCellBreaking'") as %[].
    * destruct suspender_side.
      + iDestruct "HRR" as "[HC _]".
        iDestruct (iterator_issued_exclusive with "HCellBreaking HC") as %[].
      + iDestruct "HRR" as "[HIsSus [HE|HC]]".
        2: by iDestruct (cell_breaking_token_exclusive with "HCellBreaking HC")
            as %[].
        iSplitR "HE"; last by iFrame.
        iFrame "H● HLen HDeqIdx". iApply "HRRsRestore".
        iFrame "HIsRes HCancHandle HValUnboxed".
        iExists _. iFrame "H↦". iRight. iFrame.
  - destruct suspender_side.
    + iDestruct "HRR" as "[Hptr HRR]". wp_load.
      iMod ("HClose" with "[-]") as "HΦ"; last by iModIntro.
      iDestruct "HRR" as "[$|HC]".
      2: by iDestruct (iterator_issued_exclusive with "HCellBreaking HC") as %[].
      iSplitL; last by iFrame. iFrame "H● HLen HDeqIdx".
      iApply "HRRsRestore". iFrame. iExists _. by iFrame.
    + iDestruct "HCellBreaking" as (?) "H◯".
      iDestruct (rendezvous_state_included' with "H● H◯") as %(c & HEl' & HInc).
      simplify_eq. exfalso. move: HInc=>/=. rewrite Cinl_included !pair_included.
      case=>_. case=> HContra. by apply included_None in HContra.
  - iDestruct "HRR" as "[Hptr HRR]". wp_load.
    iMod ("HClose" with "[-]") as "HΦ"; last by iModIntro.
    iFrame "HCellBreaking". iSplitL; last by iPureIntro; eexists.
    iFrame "H● HLen HDeqIdx". iApply "HRRsRestore". iFrame. iExists _. by iFrame.
Qed.

Lemma break_cell_spec γtq γa γe γd i ptr e d v:
  {{{ is_thread_queue γa γtq γe γd e d ∗
      cell_location γtq γa i ptr ∗
      rendezvous_filled_value γtq #v i ∗
      cell_breaking_token γtq i ∗ CB }}}
    CAS #ptr (InjRV #v) BROKENV
  {{{ (r: bool), RET #r; if r then V v ∗ R else E ∗ CB }}}.
Proof.
  iIntros (Φ) "(#HTq & #H↦ & #HFilled & HCellBreaking & HCB) HΦ".
  iDestruct "HTq" as "(HInv & HInfArr & _ & _)". wp_bind (CmpXchg _ _ _).
  iInv "HInv" as (l deqFront) "(>H● & HRRs & >HLen & >HDeqIdx)" "HTqClose".
  iDestruct "HLen" as %HLen.
  iDestruct (rendezvous_state_included' with "H● HFilled") as %(c & HEl & HInc).
  destruct c as [? c'|].
  2: { exfalso. simpl in *. move: HInc. rewrite csum_included.
       case; first done. case; by intros (? & ? & ? & ? & ?). }
  move: HInc. rewrite Cinl_included pair_included to_agree_included. case=> HEq _.
  simplify_eq.
  destruct c' as [[|]|]=> /=.
  - (* Rendezvous succeeded, breaking the cell is impossible, so we take E. *)
    iDestruct (big_sepL_lookup_acc with "HRRs") as "[HRR HRRsRestore]";
      first done.
    simpl. iDestruct "HRR" as "(HIsRes & HCancHandle & >% & HRR)".
    iDestruct "HRR" as (ℓ) "[H↦' HRR]".
    iDestruct (infinite_array_mapsto_agree with "H↦ H↦'") as "><-".
    iDestruct "HRR" as "[(_ & HContra & _)|(Hℓ & HIsSus & [HE|HContra])]".
    all: try by iDestruct (cell_breaking_token_exclusive
                             with "HCellBreaking HContra") as ">[]".
    wp_cmpxchg_fail. iSpecialize ("HΦ" $! false with "[$]").
    iMod ("HTqClose" with "[-HΦ]") as "_"; last by iModIntro; wp_pures.
    iExists _, _. iFrame "H● HDeqIdx". iSplitL; last by iPureIntro.
    iApply "HRRsRestore". iFrame "HIsRes HCancHandle". iSplitR; first done.
    iExists _. iFrame "H↦". iRight. iFrame.
  - (* Cell was broken before we arrived? Impossible. *)
    iDestruct "HCellBreaking" as (?) "HCellBreaking".
    iDestruct (rendezvous_state_included' with "H● HCellBreaking")
      as %(? & HEl' & HInc).
    exfalso. move: HInc. simplify_eq=>/=. rewrite Cinl_included pair_included.
    case=> _. rewrite pair_included; case=> HContra.
    by apply included_None in HContra.
  - (* Cell is still intact, so we may break it. *)
    iDestruct (big_sepL_insert_acc with "HRRs") as "[HRR HRRsRestore]";
      first done.
    simpl. iDestruct "HRR" as "(HIsRes & HCancHandle & >% & HRR)".
    iDestruct "HRR" as (ℓ) "(H↦' & Hℓ & HE & HV & HR)".
    iDestruct (infinite_array_mapsto_agree with "H↦ H↦'") as "><-".
    wp_cmpxchg_suc. iSpecialize ("HΦ" $! true with "[$]").
    iMod (break_cell_ra with "H● HCellBreaking") as "[H● #H◯]"; first done.
    iMod ("HTqClose" with "[-HΦ]") as "_"; last by iModIntro; wp_pures.
    iDestruct "HDeqIdx" as %HDeqIdx.
    iExists _, _. iFrame "H●". rewrite insert_length. iSplitL.
    2: {
      iPureIntro; split; first lia.
      case. intros ? (r & HEl' & HSkippable). apply HDeqIdx. split; first done.
      destruct (decide (i = deqFront - 1)).
      - subst. rewrite list_insert_alter list_lookup_alter HEl in HEl'.
        simpl in *. simplify_eq. contradiction.
      - rewrite list_lookup_insert_ne in HEl'; last lia.
      eexists. done.
    }
    iApply "HRRsRestore". simpl. iFrame "HIsRes HCancHandle".
    iSplitR; first done. iExists _. iFrame "H↦". iFrame "Hℓ". iLeft. iFrame.
Qed.

Lemma take_cell_value_spec γtq γa γe γd i ptr e d v:
  {{{ is_thread_queue γa γtq γe γd e d ∗
      cell_location γtq γa i ptr ∗
      rendezvous_filled_value γtq v i ∗
      iterator_issued γe i }}}
    CAS #ptr (InjRV v) TAKENV
  {{{ (r: bool) v', RET #r; ⌜v = #v'⌝ ∧ if r then V v' ∗ R else CB ∗ E }}}.
Proof.
  iIntros (Φ) "(#HTq & #H↦ & #HFilled & HIsSus) HΦ".
  iDestruct "HTq" as "(HInv & HInfArr & _ & _)". wp_bind (CmpXchg _ _ _).
  iInv "HInv" as (l deqFront) "(>H● & HRRs & >HLen & >HDeqIdx)" "HTqClose".
  iDestruct "HLen" as %HLen.
  iDestruct (rendezvous_state_included' with "H● HFilled") as %(c & HEl & HInc).
  destruct c as [? c'|].
  2: { exfalso. simpl in *. move: HInc. rewrite csum_included.
       case; first done. case; by intros (? & ? & ? & ? & ?). }
  move: HInc. rewrite Cinl_included pair_included to_agree_included. case=> HEq _.
  simplify_eq.
  iDestruct (big_sepL_insert_acc with "HRRs") as "[HRR HRRsRestore]";
    first done.
  simpl. iDestruct "HRR" as "(HIsRes & HCancHandle & >% & HRR)".
  iDestruct "HRR" as (ℓ) "[H↦' HRR]".
  iDestruct (infinite_array_mapsto_agree with "H↦ H↦'") as "><-".
  destruct c' as [[|]|]=> /=.
  - (* Rendezvous succeeded even before we arrived. *)
    iSpecialize ("HRRsRestore" $! _); rewrite list_insert_id //.
    iDestruct "HRR" as "[(Hℓ & HCellBreaking & HV & HR)|(_ & HContra & _)]".
    2: by iDestruct (iterator_issued_exclusive with "HIsSus HContra") as ">[]".
    wp_cmpxchg_suc. iSpecialize ("HΦ" $! true with "[HV HR]"). by iFrame.
    iMod ("HTqClose" with "[-HΦ]") as "_"; last by iModIntro; wp_pures.
    iExists _, _. iFrame "H● HDeqIdx". iSplitL; last by iPureIntro.
    iApply "HRRsRestore". iFrame "HIsRes HCancHandle". iSplitR; first done.
    iExists _. iFrame "H↦". iRight. iFrame.
  - (* Cell was broken before we arrived. *)
    iSpecialize ("HRRsRestore" $! _); rewrite list_insert_id //.
    iDestruct "HRR" as "(Hℓ & [[HE HCB]|HContra])".
    2: by iDestruct (iterator_issued_exclusive with "HIsSus HContra") as ">[]".
    wp_cmpxchg_fail. iSpecialize ("HΦ" $! false with "[HE HCB]"). by iFrame.
    iMod ("HTqClose" with "[-HΦ]") as "_"; last by iModIntro; wp_pures.
    iExists _, _. iFrame "H● HDeqIdx". iSplitL; last by iPureIntro.
    iApply "HRRsRestore". iFrame "HIsRes HCancHandle". iSplitR; first done.
    iExists _. iFrame "H↦". iFrame.
  - (* Cell is still intact, so we may take the value from it. *)
    iDestruct "HRR" as "(Hℓ & HE & HV & HR)".
    wp_cmpxchg_suc. iSpecialize ("HΦ" $! true with "[HV HR]"). by iFrame.
    iMod (take_cell_value_ra with "H●") as "[H● #H◯]"; first done.
    iMod ("HTqClose" with "[-HΦ]") as "_"; last by iModIntro; wp_pures.
    iDestruct "HDeqIdx" as %HDeqIdx.
    iExists _, _. iFrame "H●". rewrite insert_length. iSplitL.
    2: {
      iPureIntro; split; first lia.
      case. intros ? (r & HEl' & HSkippable). apply HDeqIdx. split; first done.
      destruct (decide (i = deqFront - 1)).
      - subst. rewrite list_insert_alter list_lookup_alter HEl in HEl'.
        simpl in *. simplify_eq. contradiction.
      - rewrite list_lookup_insert_ne in HEl'; last lia.
      eexists. done.
    }
    iApply "HRRsRestore". simpl. iFrame "HIsRes HCancHandle".
    iSplitR; first done. iExists _. iFrame "H↦". iRight. iFrame.
Qed.

(* DEALING WITH THE SUSPENDED FUTURE *******************************************)

Lemma try_cancel_cell γa γtq γe γd e d γf f i:
  NTq ## NFuture ->
  is_thread_queue γa γtq γe γd e d -∗
  rendezvous_thread_handle γtq γf f i -∗
  <<< future_cancellation_permit γf (1/2)%Qp >>>
    tryCancelFuture f @ ⊤ ∖ ↑NFuture ∖ ↑NTq
  <<< ∃ (r: bool),
      if r then future_is_cancelled γf ∗
        if immediateCancellation
        then inhabited_rendezvous_state γtq i (Some (Cinr (Cinl (to_agree ()))))
                                        ∗ ▷ cancellation_handle γa i
        else cancellation_registration_token γtq i
      else
        (∃ v, inhabited_rendezvous_state γtq i (Some (Cinl (to_agree #v))) ∗
              ▷ future_is_completed γf #v) ∗
        future_cancellation_permit γf (1/2)%Qp,
      RET #r >>>.
Proof.
  iIntros (HMask) "[#HInv _] #[HFuture H◯]". iIntros (Φ) "AU".
  awp_apply (tryCancelFuture_spec with "HFuture").
  iInv "HInv" as (l deqFront) "(>H● & HRRs & >HLen & >HDeqIdx)".
  iDestruct (rendezvous_state_included' with "H● H◯")
    as %(c & HEl & HInc).
  destruct c as [? ?|? ? r].
  { exfalso. simpl in *. move: HInc. rewrite csum_included.
    case; first done. case; by intros (? & ? & ? & ? & ?). }
  simpl in *. move: HInc. rewrite Cinr_included pair_included. case.
  rewrite to_agree_included. case=> /= ? ? _. simplify_eq.
  iDestruct (big_sepL_insert_acc with "HRRs") as "[HRR HRRsRestore]";
    first done.
  simpl.
  iDestruct "HRR" as "(HIsSus & HTh' & HRR)". iDestruct "HRR" as (ℓ) "[#H↦ HRR]".
  iApply (aacc_aupd_commit with "AU"). by solve_ndisj. iIntros "HCancPermit".
  destruct r as [[| |]|].
  (* Could not have been cancelled: we hold the permit. *)
  2: iDestruct "HRR" as "(_ & _ & HContra & _)".
  3: iDestruct "HRR" as "[HContra _]".
  all: try by iDestruct (future_cancellation_permit_implies_not_cancelled
                           with "HCancPermit HContra") as ">[]".
  - (* Cell was already resumed. *)
    iDestruct "HRR" as "(Hℓ & HIsRes & #HCompleted & HCancHandle & >HPermit)".
    iCombine "HCancPermit" "HPermit" as "HPermit'".
    rewrite -future_cancellation_permit_Fractional Qp_half_half.
    iAaccIntro with "HPermit'".
    { iIntros "HCancPermit !>".
      iEval (rewrite -Qp_half_half future_cancellation_permit_Fractional)
        in "HCancPermit".
      iDestruct "HCancPermit" as "[$ HPermit]". iIntros "$ !>".
      iExists _, _. iSpecialize ("HRRsRestore" $! _).
      rewrite list_insert_id //.
      iFrame "H● HLen HDeqIdx". iApply "HRRsRestore". simpl.
      iFrame "HIsSus HTh'". iExists _. iFrame "H↦". by iFrame. }
    iIntros (r) "Hr". destruct r.
    by iDestruct (future_is_completed_not_cancelled
                    with "HCompleted [$]") as ">[]".
    iDestruct "Hr" as "[_ HCancPermit]".
    iEval (rewrite -Qp_half_half future_cancellation_permit_Fractional)
      in "HCancPermit".
    iDestruct "HCancPermit" as "[HCancPermit HPermit]".
    iMod (resumed_cell_core_id_ra with "H●") as "[H● H◯']"; first done.
    iModIntro. iExists false. iFrame "HPermit". iSplitL "H◯'".
    { iExists _. iFrame "HCompleted". iExists _, _. iFrame "H◯'". }
    iIntros "$ !>".
    iExists _, _. iSpecialize ("HRRsRestore" $! _).
    rewrite list_insert_id //.
    iFrame "H● HLen HDeqIdx". iApply "HRRsRestore". simpl.
    iFrame "HIsSus HTh'". iExists _. iFrame "H↦". by iFrame.
  - (* Cell was neither resumed nor cancelled. *)
    iDestruct "HRR" as "(Hℓ & HCancHandle & HE & HR & >HPermit & HRR)".
    iCombine "HCancPermit" "HPermit" as "HPermit'".
    rewrite -future_cancellation_permit_Fractional Qp_half_half.
    iAaccIntro with "HPermit'".
    { iIntros "HCancPermit !>".
      iEval (rewrite -Qp_half_half future_cancellation_permit_Fractional)
        in "HCancPermit".
      iDestruct "HCancPermit" as "[$ HPermit]". iIntros "$ !>".
      iExists _, _. iSpecialize ("HRRsRestore" $! _).
      rewrite list_insert_id //.
      iFrame "H● HLen HDeqIdx". iApply "HRRsRestore". simpl.
      iFrame "HIsSus HTh'". iExists _. iFrame "H↦". by iFrame. }
    iIntros (r) "Hr". destruct r.
    2: {
      iDestruct "Hr" as "[Hr _]". iDestruct "Hr" as (?) "HFutureCompleted".
      iDestruct "HRR" as "[>HContra|[>HContra _]]".
      all: iDestruct (future_completion_permit_implies_not_completed
                        with "HContra HFutureCompleted") as %[].
    }
    iExists true. iDestruct "Hr" as "#HCancelled". iFrame "HCancelled".
    remember immediateCancellation as hi eqn: HCancellation. destruct hi.
    + iMod (immediately_cancel_cell_ra with "H●") as "[H● H◯']"; first done.
      iSplitL "H◯' HCancHandle". by iFrame; iExists _, _.
      iIntros "!> $ !>".
      iDestruct "HLen" as %HLen. iDestruct "HDeqIdx" as %HDeqIdx.
      iExists _, _. iFrame "H●". rewrite insert_length. iSplitL.
      2: {
        iPureIntro. split; first lia.
        case. intros ? (r & HEl' & HSkippable). apply HDeqIdx. split; first done.
        destruct (decide (i = deqFront - 1)).
        - subst. rewrite list_insert_alter list_lookup_alter HEl in HEl'.
          simpl in *. simplify_eq. contradiction.
        - rewrite list_lookup_insert_ne in HEl'; last lia.
        eexists. done.
      }
      iApply "HRRsRestore". iFrame. iExists _. iFrame "H↦ HCancelled".
      iSplitL "Hℓ"; first by iFrame. rewrite -HCancellation.
      iSplitR; first done. rewrite /resources_for_resumer.
      iLeft. iFrame.
    + iMod (cancel_cell_ra with "H●") as "[H● H◯']"; first done.
      iSplitL "H◯'". by iExists _, _.
      iIntros "!> $ !>".
      iDestruct "HLen" as %HLen. iDestruct "HDeqIdx" as %HDeqIdx.
      iExists _, _. iFrame "H●". rewrite insert_length. iSplitL.
      2: {
        iPureIntro. split; first lia.
        case. intros ? (r & HEl' & HSkippable). apply HDeqIdx. split; first done.
        destruct (decide (i = deqFront - 1)).
        - subst. rewrite list_insert_alter list_lookup_alter HEl in HEl'.
          simpl in *. simplify_eq. contradiction.
        - rewrite list_lookup_insert_ne in HEl'; last lia.
        eexists. done.
      }
      iApply "HRRsRestore". iFrame. iExists _. iFrame "H↦ HCancelled".
      rewrite -HCancellation. iSplitR; first by iPureIntro; case.
      iLeft. iFrame.
Qed.

Lemma try_resume_cell γa γtq γe γd e d γf f i v:
  NTq ## NFuture ->
  deq_front_at_least γtq (S i) -∗
  is_thread_queue γa γtq γe γd e d -∗
  rendezvous_thread_handle γtq γf f i -∗
  ▷ V v -∗
  <<< future_completion_permit γf (1/2)%Qp >>>
    tryCompleteFuture f #v @ ⊤ ∖ ↑NFuture ∖ ↑NTq
  <<< ∃ (r: bool),
      if r then ▷ E ∗ future_is_completed γf #v ∗
                inhabited_rendezvous_state γtq i (Some (Cinl (to_agree #v)))
      else ▷ V v ∗
           if immediateCancellation
           then ▷ R
           else inhabited_rendezvous_state γtq i (Some (Cinr (Cinr ε))) ∗
                iterator_issued γd i,
      RET #r >>>.
Proof.
  iIntros (HMask) "#HDeqFront [#HInv _] #[HFuture H◯] HV". iIntros (Φ) "AU".
  awp_apply (tryCompleteFuture_spec _ true with "HFuture"). rewrite /V'.
  iInv "HInv" as (l deqFront) "(>H● & HRRs & >HLen & >HDeqIdx)".
  iDestruct (deq_front_at_least_valid with "H● HDeqFront") as %HFront.
  iDestruct (rendezvous_state_included' with "H● H◯")
    as %(c & HEl & HInc).
  destruct c as [? ?|γf' f' r].
  { exfalso. simpl in *. move: HInc. rewrite csum_included.
    case; first done. case; by intros (? & ? & ? & ? & ?). }
  simpl in *. move: HInc. rewrite Cinr_included pair_included. case.
  rewrite to_agree_included. case=> /= ? ? _. simplify_eq.
  iDestruct (big_sepL_insert_acc with "HRRs") as "[HRR HRRsRestore]"; first done.
  rewrite bool_decide_true; last lia.
  iDestruct "HRR" as "(HIsSus & HTh' & HRR)". iDestruct "HRR" as (ℓ) "[#H↦ HRR]".
  iApply (aacc_aupd_commit with "AU"). by solve_ndisj. iIntros "HComplPermit".
  destruct r as [[| |r']|].
  - (* Cell could not have already been resumed. *)
    iDestruct "HRR" as "(_ & _ & #HCompleted & _)".
    iDestruct (future_completion_permit_implies_not_completed
                 with "HComplPermit HCompleted") as ">[]".
  - (* Cell was immediately cancelled. *)
    iDestruct "HRR" as "(Hℓ & >HImmediate & #HCancelled & HResources)".
    iDestruct "HImmediate" as %HImmediate.
    simpl. rewrite /resources_for_resumer.
    iDestruct "HResources" as "[[>[HContra|[HPermit' HIsRes]] HR]|[>HContra _]]".
    all: try by iDestruct (future_completion_permit_exclusive
                             with "HContra HComplPermit") as %[].
    iCombine "HComplPermit" "HPermit'" as "HComplPermit".
    iEval (rewrite -future_completion_permit_Fractional Qp_half_half)
      in "HComplPermit".
    iAssert (▷ V' #v ∨ ▷ future_is_cancelled γf')%I with "[]" as "HAacc'";
      first by iRight.
    iCombine "HAacc'" "HComplPermit" as "HAacc".
    iAaccIntro with "HAacc".
    { iIntros "[_ HComplPermit]".
      iEval (rewrite -Qp_half_half future_completion_permit_Fractional)
        in "HComplPermit".
      iDestruct "HComplPermit" as "[$ HComplPermit]". iIntros "!> $".
      iFrame "HV". iModIntro.
      iExists _, _. iFrame "H● HLen HDeqIdx".
      iSpecialize ("HRRsRestore" $! _). rewrite list_insert_id //.
      iApply "HRRsRestore". simpl.
      iFrame "HIsSus HTh'". iExists _. iFrame "H↦ HCancelled Hℓ".
      iSplitR; first done. iLeft. iFrame "HR". iRight. iFrame.
    }
    iIntros (r) "Hr". destruct r.
    by iDestruct (future_is_completed_not_cancelled
                    with "Hr HCancelled") as ">[]".
    iExists false.
    assert (immediateCancellation = true) as ->
        by destruct immediateCancellation=>//.
    iDestruct "Hr" as "(_ & _ & HComplPermit)". iFrame "HV HR".
    iIntros "!> $ !>". iExists _, _. iFrame.
    iSpecialize ("HRRsRestore" $! _). rewrite list_insert_id //.
    iApply "HRRsRestore". iFrame "HIsSus HTh'". iExists _.
    iFrame "H↦ HCancelled Hℓ".
    iSplitR. by destruct immediateCancellation. iRight. iFrame.
  - (* Cell was cancelled. *)
    iDestruct "HRR" as "(#HCancelled & >HNotImmediate & HRR)".
    iDestruct "HNotImmediate" as %HNotImmediate.
    iAssert (▷(future_completion_permit γf' 1%Qp ∗ iterator_issued γd i ∗
              ((iterator_issued γd i -∗ future_completion_permit γf' (1/2)%Qp -∗ cell_resources γtq γa γe γd i (Some (cellInhabited γf' f' (Some (cellCancelled r')))) true) ∧
               (future_completion_permit γf' 1%Qp -∗ cell_resources γtq γa γe γd i (Some (cellInhabited γf' f' (Some (cellCancelled r')))) true))))%I
      with "[HIsSus HTh' HRR HComplPermit]" as "(>HPermit & >HIsRes & HRestore)".
    {
      destruct r' as [[[[| ] | ] | ]|].
      - iDestruct "HRR" as "(_ & _ & >HContra)".
        iDestruct (future_completion_permit_exclusive
                     with "HContra HComplPermit") as "[]".
      - iDestruct "HRR" as "(Hℓ & HCancToken &
          [[>[HContra|[HComplPermit' HIsRes]] HAwak] | [>HContra _] ])".
        all: try iDestruct (future_completion_permit_exclusive
                              with "HContra HComplPermit") as "[]".
        iCombine "HComplPermit" "HComplPermit'" as "HComplPermit".
        rewrite -future_completion_permit_Fractional Qp_half_half.
        iFrame "HComplPermit HIsRes HIsSus HTh'". iSplit.
        + iNext. iIntros "HIsRes HComplPermit". iFrame. iExists _.
          iFrame "H↦ HCancelled Hℓ". iSplitR; first done. iLeft. iFrame. iRight.
          iFrame.
        + iNext. iIntros "HComplPermit". iFrame. iExists _.
          iFrame "H↦ HCancelled Hℓ". done.
      - iDestruct "HRR" as "(Hℓ & HE &
          [[>[HContra|[HComplPermit' HIsRes]] HAwak] | [>HContra _] ])".
        all: try iDestruct (future_completion_permit_exclusive
                              with "HContra HComplPermit") as "[]".
        iCombine "HComplPermit" "HComplPermit'" as "HComplPermit".
        rewrite -future_completion_permit_Fractional Qp_half_half.
        iFrame "HComplPermit HIsRes HIsSus HTh'". iSplit.
        + iNext. iIntros "HIsRes HComplPermit". iFrame. iExists _.
          iFrame "H↦ HCancelled Hℓ". iSplitR; first done. iLeft. iFrame. iRight.
          iFrame.
        + iNext. iIntros "HComplPermit". iFrame. iExists _.
          iFrame "H↦ HCancelled Hℓ". done.
      - iDestruct "HRR" as "($ & $ &
          [(Hℓ & HE & >[HC|[HComplPermit' HIsRes]])|[(Hℓ &
            [[>[HC|[HComplPermit' HIsRes]] HAwak] | [>HC _] ] & HTok)|HC']])";
          last iDestruct "HC'" as (?) "(_ & _ & _ & >HC & _)".
        all: try iDestruct (future_completion_permit_exclusive
                              with "HC HComplPermit") as "[]".
        all: iCombine "HComplPermit" "HComplPermit'" as "HComplPermit".
        all: rewrite -future_completion_permit_Fractional Qp_half_half.
        all: iFrame "HComplPermit HIsRes HIsSus HTh'".
        * iSplit.
          + iNext. iIntros "HIsRes HComplPermit". iFrame. iExists _.
            iFrame "H↦ HCancelled". iSplitR; first done. iLeft. iFrame. iRight.
            iFrame.
          + iNext. iIntros "HComplPermit". iExists _.
            iFrame "H↦ HCancelled". repeat (iSplitR; first done). iLeft. iFrame.
        * iSplit.
          + iNext. iIntros "HIsRes HComplPermit". iExists _.
            iFrame "H↦ HCancelled". repeat (iSplitR; first done).
            iRight. iLeft. iFrame. iLeft. iFrame. iRight. iFrame.
          + iNext. iIntros "HComplPermit". iExists _.
            iFrame "H↦ HCancelled".
            repeat (iSplitR; first done). iRight. iLeft. iFrame.
      - iDestruct "HRR" as "($ & $ & HRR)".
        iDestruct "HRR" as "[(Hℓ & HE & >[HC|[HComplPermit' HIsRes]])|
                            [_ HRR]]";
          last iDestruct "HRR" as (?) "(_ & _ & _ & >HC & _)".
        all: try iDestruct (future_completion_permit_exclusive
                              with "HC HComplPermit") as "[]".
        iCombine "HComplPermit" "HComplPermit'" as "HComplPermit".
        rewrite -future_completion_permit_Fractional Qp_half_half.
        iFrame "HComplPermit HIsRes HIsSus HTh'". iSplit.
        + iNext. iIntros "HIsRes HComplPermit". iFrame. iExists _.
          iFrame "H↦ HCancelled". iSplitR; first done. iLeft. iFrame. iRight.
          iFrame.
        + iNext. iIntros "HComplPermit". iExists _.
          iFrame "H↦ HCancelled". repeat (iSplitR; first done). iLeft. iFrame.
    }
    iAssert (▷ V' #v ∨ ▷ future_is_cancelled γf')%I with "[]" as "HAacc'";
      first by iRight.
    iCombine "HAacc'" "HPermit" as "HAacc".
    iAaccIntro with "HAacc".
    { iIntros "[_ HComplPermit]".
      iEval (rewrite -Qp_half_half future_completion_permit_Fractional)
        in "HComplPermit".
      iDestruct "HComplPermit" as "[$ HComplPermit]". iIntros "!> $".
      iFrame "HV". iModIntro.
      iExists _, _. iFrame "H● HLen HDeqIdx".
      iSpecialize ("HRRsRestore" $! _). rewrite list_insert_id //.
      iApply "HRRsRestore". iDestruct "HRestore" as "[HRestore _]".
      iApply ("HRestore" with "[$] [$]").
    }
    iIntros (r) "Hr". destruct r.
    by iDestruct (future_is_completed_not_cancelled
                 with "Hr HCancelled") as ">[]".
    iDestruct "Hr" as "(_ & _ & HComplPermit)".
    iExists false. iFrame "HV". destruct immediateCancellation=>//.
    iMod (cancelled_cell_core_id_ra with "H●") as "[H● H◯']"; first done.
    iFrame "HIsRes". iSplitL "H◯'"; first by iExists _, _.
    iIntros "!> $ !>". iExists _, _. iFrame.
    iSpecialize ("HRRsRestore" $! _). rewrite list_insert_id //.
    iApply "HRRsRestore". iDestruct "HRestore" as "[_ HRestore]".
    iApply "HRestore". iFrame "HComplPermit".
  - (* Cell was neither resumed nor cancelled. *)
    iDestruct "HRR" as "(Hℓ & HCancHandle & HE & HR & >HCancPermit &
      >[HC|[HPermit HAwak]])".
    by iDestruct (future_completion_permit_exclusive with "HC HComplPermit")
      as %[].
    iCombine "HComplPermit" "HPermit" as "HPermit'".
    rewrite -future_completion_permit_Fractional Qp_half_half.
    iAssert (▷ V' #v ∨ ▷ future_is_cancelled γf')%I
      with "[HV HR]" as "HV'"; first by iLeft; iExists _; iFrame.
    iCombine "HV'" "HPermit'" as "HAacc".
    iAaccIntro with "HAacc".
    { iIntros "HAacc". iDestruct "HAacc" as "[[HV'|HContra] HComplPermit]".
      2: {
        iDestruct (future_cancellation_permit_implies_not_cancelled with
                  "HCancPermit HContra") as ">[]".
      }
      iDestruct "HV'" as (x) "(>HEq & HV & HR)". iDestruct "HEq" as %HEq.
      simplify_eq.
      iEval (rewrite -Qp_half_half future_completion_permit_Fractional)
        in "HComplPermit".
      iDestruct "HComplPermit" as "[$ HComplPermit]". iIntros "!> $".
      iFrame "HV". iModIntro.
      iExists _, _. iFrame "H● HLen HDeqIdx".
      iSpecialize ("HRRsRestore" $! _). rewrite list_insert_id //.
      iApply "HRRsRestore". simpl.
      iFrame "HIsSus HTh'". iExists _. iFrame "H↦". iFrame. iRight. iFrame.
    }
    iIntros (r) "Hr". destruct r.
    2: {
      iDestruct "Hr" as "[Hr _]".
      iDestruct (future_cancellation_permit_implies_not_cancelled
                   with "HCancPermit Hr") as "[]".
    }
    iExists true. iDestruct "Hr" as "#HCompleted". iFrame "HCompleted HE".
    iMod (resume_cell_ra with "H●") as "[H● H◯']"; first done.
    iSplitL "H◯'". by iExists _, _.
    iIntros "!> $ !>".
    iDestruct "HLen" as %HLen. iDestruct "HDeqIdx" as %HDeqIdx.
    iExists _, _. iFrame "H●". rewrite insert_length. iSplitL.
    2: {
      iPureIntro. split; first lia.
      case. intros ? (r & HEl' & HSkippable). apply HDeqIdx. split; first done.
      destruct (decide (i = deqFront - 1)).
      - subst. rewrite list_insert_alter list_lookup_alter HEl in HEl'.
        simpl in *. simplify_eq. contradiction.
      - rewrite list_lookup_insert_ne in HEl'; last lia.
      eexists. done.
    }
    iApply "HRRsRestore". iFrame. iExists _. iFrame "H↦ HCompleted".
    by iLeft.
Qed.

Lemma await_cell γa γtq γe γd e d γf f i:
  NTq ## NFuture ->
  is_thread_queue γa γtq γe γd e d -∗
  rendezvous_thread_handle γtq γf f i -∗
  <<< future_cancellation_permit γf (1/2)%Qp >>>
    awaitFuture f @ ⊤ ∖ ↑NFuture ∖ ↑NTq
  <<< ∃ (v': base_lit), V v' ∗ R ∗ future_is_completed γf #v',
      RET (SOMEV #v') >>>.
Proof.
  iIntros (HMask) "[#HInv _] #[HFuture H◯]". iIntros (Φ) "AU".
  awp_apply (awaitFuture_spec with "HFuture").
  iInv "HInv" as (l deqFront) "(>H● & HRRs & >HLen & >HDeqIdx)".
  iDestruct (rendezvous_state_included' with "H● H◯")
    as %(c & HEl & HInc).
  destruct c as [? ?|? ? r].
  { exfalso. simpl in *. move: HInc. rewrite csum_included.
    case; first done. case; by intros (? & ? & ? & ? & ?). }
  simpl in *. move: HInc. rewrite Cinr_included pair_included. case.
  rewrite to_agree_included. case=> /= ? ? _. simplify_eq.
  iDestruct (big_sepL_lookup_acc with "HRRs") as "[HRR HRRsRestore]";
    first done.
  simpl.
  iDestruct "HRR" as "(HIsSus & HTh' & HRR)". iDestruct "HRR" as (ℓ) "[#H↦ HRR]".
  iApply (aacc_aupd_commit with "AU"). by solve_ndisj. iIntros "HCancPermit".
  destruct r as [[| |]|].
  (* Could not have been cancelled: we hold the permit. *)
  2: iDestruct "HRR" as "(_ & _ & HContra & _)".
  3: iDestruct "HRR" as "[HContra _]".
  all: try by iDestruct (future_cancellation_permit_implies_not_cancelled
                           with "HCancPermit HContra") as ">[]".
  - (* Cell was already resumed. *)
    iDestruct "HRR" as "(Hℓ & HIsRes & #HCompleted & HCancHandle & >HPermit)".
    iCombine "HCancPermit" "HPermit" as "HPermit'".
    rewrite -future_cancellation_permit_Fractional Qp_half_half.
    iAaccIntro with "HPermit'".
    { iIntros "HCancPermit !>".
      iEval (rewrite -Qp_half_half future_cancellation_permit_Fractional)
        in "HCancPermit".
      iDestruct "HCancPermit" as "[$ HPermit]". iIntros "$ !>".
      iExists _, _. iFrame "H● HLen HDeqIdx". iApply "HRRsRestore". simpl.
      iFrame "HIsSus HTh'". iExists _. iFrame "H↦". by iFrame. }
    iIntros (r) "(HV & #HCompleted' & HCancPermit)".
    iDestruct "HV" as (? HEq) "[HV HR]". simplify_eq. iExists _.
    iFrame "HV HR HCompleted'". iModIntro. iIntros "$ !>".
    iExists _, _. iFrame "H● HLen HDeqIdx". iApply "HRRsRestore". simpl.
    iFrame "HIsSus HTh'". iExists _. iFrame "H↦". by iFrame.
  - (* Cell was neither resumed nor cancelled. *)
    iDestruct "HRR" as "(Hℓ & HCancHandle & HE & HR & >HPermit & HRR)".
    iCombine "HCancPermit" "HPermit" as "HPermit'".
    rewrite -future_cancellation_permit_Fractional Qp_half_half.
    iAaccIntro with "HPermit'".
    { iIntros "HCancPermit !>".
      iEval (rewrite -Qp_half_half future_cancellation_permit_Fractional)
        in "HCancPermit".
      iDestruct "HCancPermit" as "[$ HPermit]". iIntros "$ !>".
      iExists _, _. iFrame "H● HLen HDeqIdx". iApply "HRRsRestore". simpl.
      iFrame "HIsSus HTh'". iExists _. iFrame "H↦". by iFrame. }
    iIntros (r) "(_ & HContra & _)".
    iDestruct "HRR" as "[>HC|[>HC _]]".
    all: iDestruct (future_completion_permit_implies_not_completed
                      with "HC HContra") as %[].
Qed.

(* MARKING STATES **************************************************************)

Lemma mark_cell_as_resumed γa γtq γe γd e d i ptr v:
  {{{ is_thread_queue γa γtq γe γd e d ∗
      inhabited_rendezvous_state γtq i (Some (Cinl (to_agree #v))) ∗
      cell_location γtq γa i ptr }}}
    #ptr <- RESUMEDV
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "([#HInv _] & #HResumed & #H↦) HΦ".
  iInv "HInv" as (l deqFront) "(>H● & HRRs & >HLen & >HDeqIdx)".
  iDestruct "HResumed" as (γf' f') "HResumed".
  iDestruct (rendezvous_state_included' with "H● HResumed")
            as %(c & HEl & HInc).
  destruct c as [? ?|γf f r].
  { exfalso. simpl in *. move: HInc. rewrite csum_included.
    case; first done. case; by intros (? & ? & ? & ? & ?). }
  simpl in *. move: HInc. rewrite Cinr_included pair_included. case.
  rewrite to_agree_included. case=> /= ? ? HInc'. simplify_eq.
  destruct r as [r'|]; last by apply included_None in HInc'. simpl in *.
  destruct r' as [v'| |]; simpl in *.
  - iDestruct (big_sepL_lookup_acc with "HRRs") as "[HRR HRRsRestore]";
      first done.
    simpl. iDestruct "HRR" as "(HIsSus & HTh' & HRR)".
    iDestruct "HRR" as (?) "(H↦' & Hℓ & HRR)".
    iDestruct (infinite_array_mapsto_agree with "H↦ H↦'") as "><-".
    iAssert (▷ ptr ↦ -)%I with "[Hℓ]" as (?) "Hℓ".
    { iDestruct "Hℓ" as "[Hℓ|Hℓ]"; by iExists _. }
    wp_store.
    iDestruct ("HΦ" with "[$]") as "$". iModIntro. iExists _, _.
    iFrame. iApply "HRRsRestore". iFrame. iExists _. iFrame "H↦ Hℓ".
  - exfalso. move: HInc'. rewrite Some_included; case.
    by move=> HInc; inversion HInc.
    rewrite csum_included. case; first done. case; by intros (? & ? & ? & ? & ?).
  - exfalso. move: HInc'. rewrite Some_included; case.
    by move=> HInc; inversion HInc.
    rewrite csum_included. case; first done. case; by intros (? & ? & ? & ? & ?).
Qed.

Lemma markCancelled_immediate_spec γa γtq γe γd e d i ptr:
  is_thread_queue γa γtq γe γd e d -∗
  inhabited_rendezvous_state γtq i (Some (Cinr (Cinl (to_agree ())))) -∗
  cell_location γtq γa i ptr -∗
  <<< True >>>
    getAndSet #ptr CANCELLEDV @ ⊤ ∖ ↑NTq
  <<< ∃ v, True, RET v >>>.
Proof.
  iIntros "[#HInv _] #HState #H↦" (Φ) "AU".
  awp_apply getAndSet_spec.
  iInv "HInv" as (l deqFront) "(>H● & HRRs & >HLen & >HDeqIdx)".
  iDestruct "HState" as (γf' f') "HState".
  iDestruct (rendezvous_state_included' with "H● HState") as %(c & HEl & HInc).
  assert (c = cellInhabited γf' f' (Some cellImmediatelyCancelled)) as ->.
  {
    destruct c as [|? ? r]=>//=.
    { exfalso. simpl in *. move: HInc. rewrite csum_included.
      case; first done. case; by intros (? & ? & ? & ? & ?). }
    simpl in *. move: HInc. rewrite Cinr_included pair_included. case.
    rewrite to_agree_included. case=> /= ? ? HInc'. simplify_eq.
    destruct r as [r'|]; last by apply included_None in HInc'. simpl in *.
    move: HInc'.
    destruct r' as [v'| |r'']; simpl in *.
    - rewrite Some_included. case. by intros HContra; inversion HContra.
      rewrite csum_included. case; first done.
      case; by intros (? & ? & ? & ? & ?).
    - done.
    - rewrite Some_included. rewrite Cinr_included. case.
      + intros HContra. inversion HContra. simplify_eq.
        inversion H5.
      + rewrite csum_included. case; first done.
        case; by intros (? & ? & ? & ? & ?).
  }
  iDestruct (big_sepL_lookup_acc with "HRRs") as "[HRR HRRs]"; first done.
  simpl. iDestruct "HRR" as "(HIsSus & #[HFuture HLocs] & HRR)".
  iDestruct (future_is_loc with "HFuture") as ">HLoc".
  iDestruct "HLoc" as %[fℓ ->]. iDestruct "HRR" as (ℓ) "(H↦' & Hℓ & HRest)".
  iDestruct (infinite_array_mapsto_agree with "H↦ H↦'") as "><-".
  iDestruct "Hℓ" as "[Hℓ|Hℓ]".
  1: iAssert (▷ ptr ↦ InjLV #fℓ ∧ ⌜val_is_unboxed (InjLV #fℓ)⌝)%I
    with "[Hℓ]" as "HAacc"; first by iFrame.
  2: iAssert (▷ ptr ↦ CANCELLEDV ∧ ⌜val_is_unboxed CANCELLEDV⌝)%I
    with "[Hℓ]" as "HAacc"; first by iFrame.
  all: iApply (aacc_aupd_commit with "AU"); first done; iIntros "_".
  all: iAaccIntro with "HAacc".
  - iIntros "[Hℓ _] !>". iSplitR; first done.
    iIntros "$ !>". iExists _, _. iFrame. iApply "HRRs".
    iFrame "HIsSus HFuture HLocs". iExists _. by iFrame.
  - iIntros "Hℓ !>". iExists _. iSplitR; first done. iIntros "$ !>".
    iExists _, _. iFrame. iApply "HRRs". iFrame "HIsSus HFuture HLocs".
    iExists _. by iFrame.
  - iIntros "[Hℓ _] !>". iSplitR; first done.
    iIntros "$ !>". iExists _, _. iFrame. iApply "HRRs".
    iFrame "HIsSus HFuture HLocs". iExists _. by iFrame.
  - iIntros "Hℓ !>". iExists _. iSplitR; first done. iIntros "$ !>".
    iExists _, _. iFrame. iApply "HRRs". iFrame "HIsSus HFuture HLocs".
    iExists _. by iFrame.
Qed.

Theorem register_cancellation E' γa γtq γe γd e d n i:
  ↑NTq ⊆ E' ->
  is_thread_queue γa γtq γe γd e d -∗
  cancellation_registration_token γtq i -∗
  thread_queue_state γtq n ={E'}=∗
  cell_cancelling_token γtq i ∗
  if bool_decide (n = 0)
  then thread_queue_state γtq 0 ∗ ▷ R ∗
       inhabited_rendezvous_state γtq i
         (Some (Cinr (Cinr (0, Some (Cinl (to_agree ()))))))
  else thread_queue_state γtq (n - 1) ∗ ▷ cancellation_handle γa i ∗
       inhabited_rendezvous_state γtq i
         (Some (Cinr (Cinr (0, Some (Cinr ε))))).
Proof.
  iIntros (HMask) "[#HInv _] HToken H◯". iDestruct "HToken" as (? ?) "HToken".
  iInv "HInv" as (l deqFront) "(>H● & HRRs & >HLen & >HDeqIdx)" "HClose".
  iDestruct (rendezvous_state_included' with "H● HToken") as %(c & HEl & HInc).
  assert (c = cellInhabited γf f (Some (cellCancelled None))) as ->.
  {
    destruct c as [|? ? r]=>//=.
    { exfalso. simpl in *. move: HInc. rewrite csum_included.
      case; first done. case; by intros (? & ? & ? & ? & ?). }
    simpl in *. move: HInc. rewrite Cinr_included pair_included. case.
    rewrite to_agree_included. case=> /= ? ? HInc'. simplify_eq.
    destruct r as [r'|]; last by apply included_None in HInc'. simpl in *.
    move: HInc'.
    destruct r' as [v'| |r'']; simpl in *.
    - rewrite Some_included. case. by intros HContra; inversion HContra.
      rewrite csum_included. case; first done.
      case; by intros (? & ? & ? & ? & ?).
    - rewrite Some_included. rewrite Cinr_included. case.
      + intros HContra. inversion HContra. simplify_eq.
        inversion H5.
      + rewrite csum_included. case; first done.
        case; by intros (? & ? & ? & ? & ?).
    - destruct r'' as [|].
      { simpl. rewrite Some_included. case.
        { move=> HCinr. apply Cinr_inj in HCinr. apply Cinr_inj in HCinr.
          move: HCinr. case. simpl. done. }
        rewrite Cinr_included Cinr_included prod_included /= nat_included.
        case; lia. }
      done.
  }
  iDestruct (big_sepL_insert_acc with "HRRs") as "[HRR HRRs]"; first done.
  simpl. iDestruct "HRR" as "(HIsSus & HTh & HRR)".
  iDestruct "HRR" as (ℓ) "(H↦ & HFutureCancelled & HNotImmediate & HRR)".
  iDestruct "HRR" as "(HCancHandle & HR & HContents)".
  iDestruct (thread_queue_state_valid with "H● H◯") as %->.
  remember (count_matching _ _) as n eqn:HCountMatching.
  destruct n.
  - (* There are no cells left to awaken. *)
    destruct (decide (deqFront ≤ i)) as [?|HLeDeqFront].
    { (* Impossible: we know that there are no alive cells, but we are alive. *)
      exfalso.
      assert (∃ k, drop deqFront l !! (i - deqFront) = Some k ∧
                   is_nonskippable k) as (k & HEl' & HNonSkippable).
      { eexists. rewrite lookup_drop. replace (_ + (_ - _)) with i by lia.
        by split. }
      symmetry in HCountMatching. move: HCountMatching.
      rewrite count_matching_none. move=> HCountMatching.
      assert (¬ is_nonskippable k); last contradiction.
      apply HCountMatching, elem_of_list_lookup. eauto. }
    iMod (abandon_cell_ra with "H● [HToken]")
      as "(H● & HToken & HAbandoned)"; first done.
    { by iExists _, _. }
    rewrite bool_decide_true; last lia.
    rewrite bool_decide_true; last lia.
    iFrame "H◯ HR".
    iMod ("HClose" with "[-HToken HAbandoned]") as "_".
    {
      iExists _, _. iFrame "H●". rewrite insert_length.
      iDestruct "HLen" as %HLen. iDestruct "HDeqIdx" as %HDeqIdx.
      iSplitL.
      2: {
        iPureIntro. split; first lia.
        case. intros ? (r & HEl' & HSkippable). apply HDeqIdx.
        split; first done. destruct (decide (i = deqFront - 1)).
        - subst. rewrite list_insert_alter list_lookup_alter HEl in HEl'.
          simpl in *. simplify_eq. contradiction.
        - rewrite list_lookup_insert_ne in HEl'; last lia.
        eexists. done.
      }
      iApply "HRRs". iFrame "HIsSus HTh". iExists _.
      iFrame "H↦ HFutureCancelled HNotImmediate HCancHandle".
      iDestruct "HContents" as "[HContents|HContents]"; first by iLeft.
      iDestruct "HContents" as "[_ HContents]". iRight. iRight. done.
    }
    iModIntro. iSplitL "HToken"; iExists _, _; iFrame.
  - (* We may defer our awakening to another cell. *)
    iEval (rewrite bool_decide_false; last lia). iFrame "HCancHandle".
    destruct (decide (deqFront ≤ i)) as [HGeDeqFront|HLtDeqFront].
    + iMod (allow_cell_cancellation_outside_deqFront_ra with "H● H◯ [HToken]")
           as "(H● & $ & HCancellingToken & #HState)"; try done.
      by iExists _, _.
      iMod ("HClose" with "[-HCancellingToken]") as "_".
      2: iModIntro; iSplitL; by iExists _, _.
      iExists _, _. iFrame "H●". rewrite insert_length.
      iDestruct "HLen" as %HLen; iDestruct "HDeqIdx" as %HDeqIdx.
      iSplitL.
      2: {
        iPureIntro. split; first lia.
        case. intros ? (r & HEl' & HSkippable). apply HDeqIdx. split; first done.
        destruct (decide (i = deqFront - 1)). by lia.
        rewrite list_lookup_insert_ne in HEl'; last lia.
        eexists. done.
      }
      iApply "HRRs". rewrite bool_decide_false; last lia.
      simpl. iFrame "HIsSus HTh". iExists _.
      iFrame "H↦ HFutureCancelled HNotImmediate".
      iDestruct "HContents" as "[($ & $ & HContents)|[>% _]]"; last lia.
      iLeft. iFrame.
    + rewrite bool_decide_true; last lia.
      assert (is_Some (find_index is_nonskippable (drop deqFront l)))
             as [j HFindSome].
      { apply count_matching_find_index_Some. lia. }
      iMod (allow_cell_cancellation_inside_deqFront_ra with "H● H◯ [HToken]")
           as "(H● & HAwaks & $ & #HDeqFront & HCancellingToken & #HState)";
        try done.
      by rewrite drop_insert_gt; last lia.
      lia.
      by iExists _, _.
      iDestruct "HContents" as "[HContents|[_ HContents]]".
      * iMod ("HClose" with "[-HCancellingToken]") as "_".
        2: iModIntro; iSplitL; by iExists _, _.
        iExists _, _. iFrame "H●".
        iDestruct "HLen" as "_"; iDestruct "HDeqIdx" as "_".
        iSplitL.
        simpl. iDestruct "HAwaks" as "[HAwak HAwaks]".
        iDestruct ("HRRs" $! (Some (cellInhabited γf f (Some (cellCancelled (Some (cancellationAllowed None))))))
                    with "[-HAwaks HR]") as "HRRs".
        { iFrame. iExists _. iFrame.
          iDestruct "HContents" as "($ & $ & HFuture)". iLeft. iFrame. }
        iDestruct (advance_deqFront with "HAwaks HR HRRs") as "$".
        by rewrite drop_insert_gt; last lia.
        iPureIntro. apply advance_deqFront_pure.
        by rewrite drop_insert_gt; last lia.
      * iDestruct "HContents" as (v) "(HUnboxed & Hℓ & HIsres & HFuture & HV)".
        iMod (put_value_in_cancelled_cell_ra v with "H●")
             as "[H● #HState']".
        { erewrite list_lookup_insert. done.
          by eapply lookup_lt_Some. }
        rewrite list_insert_insert.
        iMod ("HClose" with "[-HCancellingToken]") as "_".
        2: iModIntro; iSplitL; by iExists _, _.
        iExists _, _. iFrame "H●".
        iDestruct "HLen" as "_"; iDestruct "HDeqIdx" as "_".
        iSplitL.
        simpl. iDestruct "HAwaks" as "[HAwak HAwaks]".
        iDestruct ("HRRs" $! (Some (cellInhabited γf f (Some (cellCancelled (Some (cancellationAllowed (Some (cellTookValue v))))))))
                    with "[-HAwaks HR]") as "HRRs".
        { iFrame. iExists _. iFrame "H↦". iLeft. iFrame. }
        iDestruct (advance_deqFront with "HAwaks HR HRRs") as "$".
        by rewrite drop_insert_gt; last lia.
        iPureIntro. apply advance_deqFront_pure.
        by rewrite drop_insert_gt; last lia.
Qed.

Lemma markCancelled_spec γa γtq γe γd e d i ptr γf f:
  is_thread_queue γa γtq γe γd e d -∗
  inhabited_rendezvous_state γtq i (Some (Cinr (Cinr (0, Some (Cinr ε))))) -∗
  cell_location γtq γa i ptr -∗ cell_cancelling_token γtq i -∗
  rendezvous_thread_handle γtq γf f i -∗
  <<< True >>>
    getAndSet #ptr CANCELLEDV @ ⊤ ∖ ↑NTq
  <<< ∃ v, ⌜v = InjLV f⌝ ∧ ▷ E ∨
      (∃ v' : base_lit,
      ⌜v = InjRV #v'⌝
      ∧ inhabited_rendezvous_state γtq i
          (Some (Cinr (Cinr (0, Some (Cinr (Some (Cinl (to_agree #v'))))))))
      ∗ awakening_permit γtq
      ∗ ▷ V v'), RET v >>>.
Proof.
  iIntros "[#HInv _] #HState #H↦ HToken #HTh" (Φ) "AU".
  iDestruct "HToken" as (? ?) "HToken".
  awp_apply getAndSet_spec.
  iInv "HInv" as (l deqFront) "(>H● & HRRs & >HLen & >HDeqIdx)".
  iDestruct "HState" as (γf' f') "HState".
  iDestruct (rendezvous_state_included' with "H● HState") as %(c & HEl & HInc).
  assert (∃ d, c = cellInhabited γf' f' (Some (cellCancelled (Some (cancellationAllowed d))))) as [d' ->].
  {
    destruct c as [|? ? r]=>//=.
    { exfalso. simpl in *. move: HInc. rewrite csum_included.
      case; first done. case; by intros (? & ? & ? & ? & ?). }
    simpl in *. move: HInc. rewrite Cinr_included pair_included. case.
    rewrite to_agree_included. case=> /= ? ? HInc'. simplify_eq.
    destruct r as [r'|]; last by apply included_None in HInc'. simpl in *.
    move: HInc'.
    destruct r' as [v'| |r'']; simpl in *.
    - rewrite Some_included. case. by intros HContra; inversion HContra.
      rewrite csum_included. case; first done.
      case; by intros (? & ? & ? & ? & ?).
    - rewrite Some_included. rewrite Cinr_included. case.
      + intros HContra. inversion HContra. simplify_eq.
        inversion H5.
      + rewrite csum_included. case; first done.
        case; by intros (? & ? & ? & ? & ?).
    - destruct r'' as [r'''|].
      2: { simpl. rewrite Some_included. case.
        { move=> HCinr. apply Cinr_inj in HCinr. apply Cinr_inj in HCinr.
          move: HCinr. case. simpl. done. }
        rewrite Cinr_included Cinr_included prod_included /= nat_included.
        case=> _ HContra. by apply included_None in HContra. }
      destruct r'''.
      2: {
        simpl. rewrite Some_included. case.
        { move=> HCinr. apply Cinr_inj in HCinr. apply Cinr_inj in HCinr.
          move: HCinr. case. simpl. done. }
        rewrite Cinr_included Cinr_included prod_included /= nat_included.
        rewrite Some_included. case=> _. case.
        intros HContra; by inversion HContra.
        rewrite csum_included.
        case; first done. case; by intros (? & ? & ? & ? & ?).
      }
      simpl. by eexists.
  }
  iDestruct (big_sepL_insert_acc with "HRRs") as "[HRR HRRs]"; first done.
  simpl. iDestruct "HRR" as "(HIsSus & #HTh' & HRR)".
  iDestruct "HTh" as "[HFutureLoc HTh]".
  iDestruct (rendezvous_state_included' with "H● HTh")
    as %(c' & HEl' & HInc').
  simplify_eq. simpl in *. move: HInc'. rewrite Cinr_included pair_included.
  rewrite to_agree_included. case. case=> /= HH1 HH2 _. simplify_eq.
  iDestruct "HRR" as (ℓ) "(H↦' & HFutureCancelled & HNotImmediate & HRR)".
  iAssert (own γtq (cell_list_contents_auth_ra l deqFront) -∗
           cell_cancelling_token γtq i -∗
           cell_cancelling_token γtq i -∗ False)%I with "[]" as "HNotFinished".
  {
    iIntros "H● HToken HToken'".
    iDestruct "HToken" as (? ?) "HToken". iDestruct "HToken'" as (? ?) "HToken'".
    iCombine "HToken" "HToken'" as "HToken". rewrite list_singletonM_op.
    iDestruct (rendezvous_state_included' with "H● HToken")
      as %(c''' & HEl'' & HInc'').
    exfalso. simplify_eq. simpl in *.
    move: HInc''. rewrite -Cinr_op Cinr_included pair_included. case=> _/=.
    rewrite Some_included. case.
    - move=> HContra. do 2 apply Cinr_inj in HContra. case HContra.
      simpl. by case.
    - do 2 rewrite Cinr_included. rewrite pair_included. case=> /=.
      rewrite nat_included nat_op_plus. lia.
  }
  iDestruct (infinite_array_mapsto_agree with "H↦ H↦'") as "><-".
  destruct d' as [[|]|].
  2: { (* Only we could have finished the cancellation. *)
    iDestruct "HRR" as "(_ & >HToken' & _)".
    iDestruct ("HNotFinished" with "H● HToken' [HToken]") as %[].
    by iExists _, _.
  }
  - (* a value was passed to the cell. *)
    iDestruct "HRR" as "([(Hℓ & >HUnboxed & HV & >HAwak)|(_ & >HToken')] &
                        HIsRes & HFuture)".
    2: { iDestruct ("HNotFinished" with "H● HToken' [HToken]") as %[].
         by iExists _, _. }
    iDestruct "HUnboxed" as %HUnboxed.
    iAssert (▷ ptr ↦ InjRV #v ∧ ⌜val_is_unboxed (InjRV #v)⌝)%I
            with "[Hℓ]" as "HAacc"; first by iFrame.
    iApply (aacc_aupd_commit with "AU"); first done. iIntros "_".
    iAaccIntro with "HAacc".
    { iIntros "[Hℓ _] !>". iSplitR; first done. iFrame "HToken". iIntros "$ !>".
      iExists _, _. iSpecialize ("HRRs" $! _). rewrite list_insert_id; last done.
      iFrame "H● HLen HDeqIdx". iApply "HRRs". iFrame "HIsSus HTh'".
      iExists _. iFrame "H↦". iFrame "HFutureCancelled HNotImmediate".
      iFrame "HIsRes HFuture". iLeft. by iFrame. }
    iIntros "Hℓ". iExists _. iMod (own_update with "H●") as "[H● H◯]".
    2: iSplitL "H◯ HV HAwak".
    2: { iModIntro. iRight; iExists _. iFrame "HV HAwak". iSplitR; first done.
      iExists _, _. iFrame. }
    {
      apply auth_update_core_id. apply _. apply prod_included. simpl.
      split; first by apply ucmra_unit_least. apply prod_included. simpl.
      split; last by apply ucmra_unit_least. apply list_singletonM_included.
      eexists. rewrite map_lookup HEl=> /=. split; first done.
      apply Some_included. right. apply Cinr_included. apply prod_included'.
      split=> /=; first done. apply Some_included. right.
      do 2 apply Cinr_included. apply prod_included=> /=. split; last done.
      apply nat_included. lia.
    }
    iIntros "!> $ !>".
    iSpecialize ("HRRs" $! _). rewrite list_insert_id; last done.
    iModIntro.
    iExists _, _. iFrame. iApply "HRRs". iFrame. iFrame "HTh'". iExists _.
    iFrame "H↦". iRight. iFrame "Hℓ". by iExists _, _.
  - (* we may cancel the cell without obstructions. *)
    iDestruct (future_is_loc with "HFutureLoc") as %[fℓ ->].
    iDestruct "HRR" as "(Hℓ & HE & HRR)".
    iAssert (▷ ptr ↦ InjLV #fℓ ∧ ⌜val_is_unboxed (InjLV #fℓ)⌝)%I
      with "[Hℓ]" as "HAacc"; first by iFrame.
    iApply (aacc_aupd_commit with "AU"); first done. iIntros "_".
    iAaccIntro with "HAacc".
    { iIntros "[Hℓ _] !>". iFrame "HToken". iIntros "$ !>". iExists _, _.
      iSpecialize ("HRRs" $! _). rewrite list_insert_id; last done.
      iFrame "H● HLen HDeqIdx". iApply "HRRs". iFrame "HIsSus HTh'".
      iExists _. iFrame "H↦". iFrame "HFutureCancelled HNotImmediate".
      iFrame "Hℓ HE HRR". }
    iIntros "Hℓ".
    iMod (finish_cancellation_ra with "H●") as "[H● #H◯]"; first done.
    iModIntro. iExists _. iSplitL "HE"; first by iLeft; iFrame.
    iIntros "$ !>".
    iExists _, _. iFrame "H●". rewrite insert_length.
    iDestruct "HLen" as %HLen; iDestruct "HDeqIdx" as %HDeqIdx.
    iSplitL.
    2: {
      iPureIntro. split; first lia.
      case. intros ? (r & HEl' & HSkippable). apply HDeqIdx. split; first done.
      destruct (decide (i = deqFront - 1)) as [->|HNeq].
      - rewrite list_lookup_insert in HEl'; last lia. simplify_eq.
        eexists. by split.
      - rewrite list_lookup_insert_ne in HEl'; last lia.
        eexists. done.
    }
    iApply "HRRs". iFrame "HIsSus HTh'". iExists _.
    iFrame "H↦ HFutureCancelled HNotImmediate Hℓ". iSplitL "HToken".
    by iExists _, _.
    rewrite /resources_for_resumer.
    iDestruct "HRR" as "[[H1 H2]|[H1 H2]]"; [iLeft|iRight]; iFrame.
Qed.

Lemma markRefused_spec γa γtq γe γd e d i ptr γf f:
  is_thread_queue γa γtq γe γd e d -∗
  inhabited_rendezvous_state γtq i (Some (Cinr (Cinr (0, Some (Cinl (to_agree ())))))) -∗
  cell_location γtq γa i ptr -∗
  cell_cancelling_token γtq i -∗
  rendezvous_thread_handle γtq γf f i -∗
  ▷ ERefuse -∗
  <<< True >>>
    getAndSet #ptr REFUSEDV @ ⊤ ∖ ↑NTq
  <<< ∃ v, ⌜v = InjLV f⌝ ∧ ▷ E
      ∨ (∃ v' : base_lit, ⌜v = InjRV #v'⌝ ∗ ▷ ERefuse ∗ ▷ V v'), RET v >>>.
Proof.
  iIntros "[#HInv _] #HState #H↦ HToken #HTh HERefuse" (Φ) "AU".
  iDestruct "HToken" as (? ?) "HToken".
  awp_apply getAndSet_spec.
  iInv "HInv" as (l deqFront) "(>H● & HRRs & >HLen & >HDeqIdx)".
  iDestruct "HState" as (γf' f') "HState".
  iDestruct (rendezvous_state_included' with "H● HState") as %(c & HEl & HInc).
  assert (c = cellInhabited γf' f' (Some (cellCancelled (Some cancellationPrevented)))) as ->.
  {
    destruct c as [|? ? r]=>//=.
    { exfalso. simpl in *. move: HInc. rewrite csum_included.
      case; first done. case; by intros (? & ? & ? & ? & ?). }
    simpl in *. move: HInc. rewrite Cinr_included pair_included. case.
    rewrite to_agree_included. case=> /= ? ? HInc'. simplify_eq.
    destruct r as [r'|]; last by apply included_None in HInc'. simpl in *.
    move: HInc'.
    destruct r' as [v'| |r'']; simpl in *.
    - rewrite Some_included. case. by intros HContra; inversion HContra.
      rewrite csum_included. case; first done.
      case; by intros (? & ? & ? & ? & ?).
    - rewrite Some_included. rewrite Cinr_included. case.
      + intros HContra. inversion HContra. simplify_eq.
        inversion H5.
      + rewrite csum_included. case; first done.
        case; by intros (? & ? & ? & ? & ?).
    - destruct r'' as [r'''|].
      2: { simpl. rewrite Some_included. case.
        { move=> HCinr. apply Cinr_inj in HCinr. apply Cinr_inj in HCinr.
          move: HCinr. case. simpl. done. }
        rewrite Cinr_included Cinr_included prod_included /= nat_included.
        case=> _ HContra. by apply included_None in HContra. }
      destruct r'''; last done.
      {
        simpl. rewrite Some_included. case.
        { move=> HCinr. apply Cinr_inj in HCinr. apply Cinr_inj in HCinr.
          move: HCinr. case. simpl. done. }
        rewrite Cinr_included Cinr_included prod_included /= nat_included.
        rewrite Some_included. case=> _. case.
        intros HContra; by inversion HContra.
        rewrite csum_included.
        case; first done. case; by intros (? & ? & ? & ? & ?).
      }
  }
  iDestruct (big_sepL_lookup_acc with "HRRs") as "[HRR HRRs]"; first done.
  simpl. iDestruct "HRR" as "(HIsSus & #HTh' & HRR)".
  iDestruct "HTh" as "[HFutureLoc HTh]".
  iDestruct (rendezvous_state_included' with "H● HTh")
    as %(c' & HEl' & HInc').
  simplify_eq. simpl in *. move: HInc'. rewrite Cinr_included pair_included.
  rewrite to_agree_included. case. case=> /= HH1 HH2 _. simplify_eq.
  iDestruct "HRR" as (ℓ) "(H↦' & HFutureCancelled & HNotImmediate & HRR)".
  iAssert (own γtq (cell_list_contents_auth_ra l deqFront) -∗
           cell_cancelling_token γtq i -∗
           cell_cancelling_token γtq i -∗ False)%I with "[]" as "HNotFinished".
  {
    iIntros "H● HToken HToken'".
    iDestruct "HToken" as (? ?) "HToken". iDestruct "HToken'" as (? ?) "HToken'".
    iCombine "HToken" "HToken'" as "HToken". rewrite list_singletonM_op.
    iDestruct (rendezvous_state_included' with "H● HToken")
      as %(c''' & HEl'' & HInc'').
    exfalso. simplify_eq. simpl in *.
    move: HInc''. rewrite -Cinr_op Cinr_included pair_included. case=> _/=.
    rewrite Some_included. case.
    - move=> HContra. do 2 apply Cinr_inj in HContra. case HContra.
      simpl. by case.
    - do 2 rewrite Cinr_included. rewrite pair_included. case=> /=.
      rewrite nat_included nat_op_plus. lia.
  }
  iDestruct (infinite_array_mapsto_agree with "H↦ H↦'") as "><-".
  iDestruct "HRR" as "(HInside & HCancHandle & HRR)".
  iDestruct "HRR" as "[(Hℓ & HE & HRes)|[(_ & _ & HToken')|HRR]]".
  2: { (* Only we could have finished the cancellation. *)
    iDestruct ("HNotFinished" with "H● HToken' [HToken]") as ">[]".
    by iExists _, _.
  }
  - (* we may mark the cell as refused without obstructions. *)
    iDestruct (future_is_loc with "HFutureLoc") as %[fℓ ->].
    iAssert (▷ ptr ↦ InjLV #fℓ ∧ ⌜val_is_unboxed (InjLV #fℓ)⌝)%I
      with "[Hℓ]" as "HAacc"; first by iFrame.
    iApply (aacc_aupd_commit with "AU"); first done. iIntros "_".
    iAaccIntro with "HAacc".
    { iIntros "[Hℓ _] !>". iFrame "HToken HERefuse". iIntros "$ !>". iExists _, _.
      iFrame "H● HLen HDeqIdx". iApply "HRRs". iFrame "HIsSus HTh'".
      iExists _. iFrame "H↦". iFrame "HFutureCancelled HNotImmediate".
      iFrame "HInside HCancHandle". iLeft. iFrame. }
    iIntros "Hℓ". iModIntro. iExists _. iSplitL "HE"; first by iLeft; iFrame.
    iIntros "$ !>". iExists _, _. iFrame "H● HLen HDeqIdx".
    iApply "HRRs". iFrame "HIsSus HTh'". iExists _.
    iFrame "H↦ HFutureCancelled HNotImmediate HInside HCancHandle".
    iRight. iLeft. iFrame "Hℓ". iSplitR "HToken"; last by iExists _, _.
    iLeft. iFrame.
  - (* a value was passed to the cell *)
    iDestruct "HRR" as (v) "(>HUnboxed & Hℓ & HIsRes & HFuture & HV)".
    iDestruct "HUnboxed" as %HUnboxed.
    iAssert (▷ ptr ↦ InjRV #v ∧ ⌜val_is_unboxed (InjRV #v)⌝)%I
            with "[Hℓ]" as "HAacc"; first by iFrame.
    iApply (aacc_aupd_commit with "AU"); first done. iIntros "_".
    iAaccIntro with "HAacc".
    { iIntros "[Hℓ _] !>". iFrame "HToken HERefuse". iIntros "$ !>". iExists _, _.
      iFrame "H● HLen HDeqIdx". iApply "HRRs". iFrame "HIsSus HTh'".
      iExists _. iFrame "H↦".
      iFrame "HFutureCancelled HNotImmediate HInside HCancHandle".
      iRight. iRight. iExists _. by iFrame. }
    iIntros "Hℓ". iModIntro. iExists _. iSplitL "HERefuse HV".
    { iRight; iExists _; by iFrame. }
    iIntros "$ !>". iExists _, _. iFrame "H● HLen HDeqIdx". iApply "HRRs".
    iFrame "HIsSus HTh'". iExists _.
    iFrame "H↦ HFutureCancelled HNotImmediate HInside HCancHandle".
    iRight. iLeft. iFrame "Hℓ". iSplitR "HToken"; last by iExists _, _.
    iRight. iFrame.
Qed.

Lemma pass_value_to_cancelled_cell_spec γa γtq γe γd e d i ptr γf f v:
  {{{ is_thread_queue γa γtq γe γd e d ∗
      inhabited_rendezvous_state γtq i (Some (Cinr (Cinr ε))) ∗
      cell_location γtq γa i ptr ∗ iterator_issued γd i ∗
      deq_front_at_least γtq (S i) ∗
      rendezvous_thread_handle γtq γf f i ∗ V v ∗ ⌜lit_is_unboxed v⌝ }}}
    CAS #ptr (InjLV f) (InjRV #v)
  {{{ (r: bool), RET #r;
      if r then E else iterator_issued γd i ∗ V v
  }}}.
Proof.
  iIntros (Φ) "([#HInv _] & #HState & #H↦ & HIsRes & #HDeqFront & #HTh & HV) HΦ".
  iDestruct "HV" as "[HV HVUnboxed]". wp_bind (CmpXchg _ _ _).
  iInv "HInv" as (l deqFront) "(>H● & HRRs & >HLen & >HDeqIdx)" "HClose".
  iDestruct "HState" as (γf' f') "HState".
  iDestruct (rendezvous_state_included' with "H● HState") as %(c & HEl & HInc).
  assert (∃ d, c = cellInhabited γf' f' (Some (cellCancelled d))) as [d' ->].
  {
    destruct c as [|? ? r]=>//=.
    { exfalso. simpl in *. move: HInc. rewrite csum_included.
      case; first done. case; by intros (? & ? & ? & ? & ?). }
    simpl in *. move: HInc. rewrite Cinr_included pair_included. case.
    rewrite to_agree_included. case=> /= ? ? HInc'. simplify_eq.
    destruct r as [r'|]; last by apply included_None in HInc'. simpl in *.
    move: HInc'.
    destruct r' as [v'| |r'']; simpl in *.
    - rewrite Some_included. case. by intros HContra; inversion HContra.
      rewrite csum_included. case; first done.
      case; by intros (? & ? & ? & ? & ?).
    - rewrite Some_included. rewrite Cinr_included. case.
      + intros HContra. inversion HContra. simplify_eq.
        inversion H5.
      + rewrite csum_included. case; first done.
        case; by intros (? & ? & ? & ? & ?).
    - by eexists.
  }
  iDestruct (big_sepL_insert_acc with "HRRs") as "[HRR HRRs]"; first done.
  iDestruct (deq_front_at_least_valid with "H● HDeqFront") as %HDF.
  rewrite bool_decide_true; last lia.
  simpl. iDestruct "HRR" as "(HIsSus & #HTh' & HRR)".
  iDestruct "HTh" as "[HFutureLoc HTh]".
  iDestruct (rendezvous_state_included' with "H● HTh")
    as %(c' & HEl' & HInc').
  simplify_eq. simpl in *. move: HInc'. rewrite Cinr_included pair_included.
  rewrite to_agree_included. case. case=> /= HH1 HH2 _. simplify_eq.
  iDestruct "HRR" as (ℓ) "(H↦' & HFutureCancelled & HNotImmediate & HRR)".
  iDestruct (infinite_array_mapsto_agree with "H↦ H↦'") as "><-".
  iDestruct (future_is_loc with "HFutureLoc") as %[fℓ ->].
  destruct d' as [[[[|]|]|]|].
  - (* We could not have already taken the value, we hold the permit. *)
    iDestruct "HRR" as "(_ & >HC & _)".
    iDestruct (iterator_issued_exclusive with "HC HIsRes") as %[].
  - (* Maybe the cell is already closed. *)
    iDestruct "HRR" as "(Hℓ & HCancTok & [[[HFuture|[_ >HC]] HAwak]|[_ >HC]])".
    all: try by iDestruct (iterator_issued_exclusive with "HC HIsRes") as %[].
    wp_cmpxchg_fail.
    iSpecialize ("HΦ" $! false with "[HIsRes HV]"); first by iFrame.
    iMod ("HClose" with "[-HΦ]") as "_"; last by iModIntro; wp_pures.
    iExists _, _. iFrame "H● HLen HDeqIdx". iSpecialize ("HRRs" $! _).
    rewrite list_insert_id; last done. iApply "HRRs".
    iFrame "HIsSus HTh'". iExists _. iFrame "H↦ HFutureCancelled HNotImmediate".
    iFrame "Hℓ HCancTok". iLeft. iFrame.
  - (* Cancellation was permitted but undecided until we arrived. *)
    iDestruct "HRR" as "(Hℓ & HE & [[[HFuture|[_ >HC]] HAwak]|[_ >HC]])".
    all: try by iDestruct (iterator_issued_exclusive with "HC HIsRes") as %[].
    iMod (put_value_in_cancelled_cell_ra with "H●") as "[H● H◯]"; first done.
    wp_cmpxchg_suc. iSpecialize ("HΦ" $! true with "HE").
    iMod ("HClose" with "[-HΦ]"); last by iModIntro; wp_pures.
    iExists _, _. iFrame "H●". rewrite insert_length.
    iDestruct "HLen" as %HLen; iDestruct "HDeqIdx" as %HDeqIdx.
    iSplitL.
    2: {
      iPureIntro. split; first lia.
      case. intros ? (r & HEl' & HSkippable). apply HDeqIdx. split; first done.
      destruct (decide (i = deqFront - 1)) as [->|HNeq].
      - rewrite list_lookup_insert in HEl'; last lia. simplify_eq.
        eexists. by split.
      - rewrite list_lookup_insert_ne in HEl'; last lia.
        eexists. done.
    }
    iApply "HRRs". iFrame "HIsSus HTh'". iExists _.
    iFrame "H↦ HFutureCancelled HNotImmediate HIsRes HFuture". iLeft.
    iFrame.
  - (* The cancellation was prevented. *)
    iDestruct "HRR" as "(_ & HCancHandle & [(Hℓ & HE & [HFuture|[_ >HC]])|
      [(Hℓ & [[[HFuture|[_ >HC]] HERefuse]|[_ >HC]] & HCancToken)|HRR]])";
      last iDestruct "HRR" as (?) "(_ & _ & >HC & _)".
    all: try by iDestruct (iterator_issued_exclusive with "HC HIsRes") as %[].
    + (* The cell is still not marked as refused. *)
      wp_cmpxchg_suc. iSpecialize ("HΦ" $! true with "HE").
      iMod ("HClose" with "[-HΦ]") as "_"; last by iModIntro; wp_pures.
      iExists _, _. iFrame "H● HLen HDeqIdx". iSpecialize ("HRRs" $! _).
      rewrite list_insert_id; last done. iApply "HRRs".
      iFrame "HIsSus HTh'". iExists _.
      iFrame "H↦ HFutureCancelled HNotImmediate HCancHandle".
      iRight. iRight. iExists _. by iFrame.
    + (* The cell is already marked as refused. *)
      wp_cmpxchg_fail.
      iSpecialize ("HΦ" $! false with "[HIsRes HV]"); first by iFrame.
      iMod ("HClose" with "[-HΦ]") as "_"; last by iModIntro; wp_pures.
      iExists _, _. iFrame "H● HLen HDeqIdx". iSpecialize ("HRRs" $! _).
      rewrite list_insert_id; last done. iApply "HRRs".
      iFrame "HIsSus HTh'". iExists _.
      iFrame "H↦ HFutureCancelled HNotImmediate HCancHandle".
      iRight. iLeft. iFrame. by iLeft.
  - (* The cancellation was not even registered yet. *)
    iDestruct "HRR" as "(HCancHandle & HR &
      [(Hℓ & HE & [HFuture|[_ >HC]])|[_ HRR]])";
      last iDestruct "HRR" as (?) "(_ & _ & >HC & _)".
    all: try by iDestruct (iterator_issued_exclusive with "HC HIsRes") as %[].
    wp_cmpxchg_suc. iSpecialize ("HΦ" $! true with "HE").
    iMod ("HClose" with "[-HΦ]") as "_"; last by iModIntro; wp_pures.
    iExists _, _. iFrame "H● HLen HDeqIdx". iSpecialize ("HRRs" $! _).
      rewrite list_insert_id; last done. iApply "HRRs".
    iFrame "HIsSus HTh'". iExists _. iFrame "H↦ HFutureCancelled HNotImmediate".
    iFrame "HCancHandle HR". iRight. iFrame. iExists _. by iFrame.
Qed.

(* WHOLE OPERATIONS ON THE THREAD QUEUE ****************************************)

Lemma tryResume_spec (mayBreakCells shouldAdjust waitForResolution: bool)
      (returnRefusedValue: val) (maxWait: nat) γa γtq γe γd e d v:
  NTq ## NFuture ->
  lit_is_unboxed v ->
  shouldAdjust = negb immediateCancellation ->
  {{{ ERefuse ∗ V v }}}
    returnRefusedValue #v
  {{{ RET #(); ▷ E }}} -∗
  {{{ is_thread_queue γa γtq γe γd e d ∗ awakening_permit γtq ∗
      V v ∗ if mayBreakCells then CB else True }}}
    tryResume array_interface #maxWait #shouldAdjust #mayBreakCells #waitForResolution
      d returnRefusedValue #v
  {{{ (n: nat), RET #n; ⌜n = 0⌝ ∧ E ∗ (if mayBreakCells then CB else True) ∨ 
                      ⌜n = 1⌝ ∧ V v ∗ (if mayBreakCells then CB else True) ∗
                        (if immediateCancellation then R
                         else awakening_permit γtq) ∨
                      ⌜n = 2 ∧ mayBreakCells⌝ ∧ R ∗ V v
  }}}.
Proof.
  iIntros (HMask HUnboxed ->) "#HRefusedValue".
  iIntros "!>" (Φ) "(#HTq & HAwak & HV & HCB) HΦ".
  wp_lam. wp_pures. wp_bind (iteratorStepOrIncreaseCounter _ _ _).
  iApply (iteratorStepOrIncreaseCounter_spec _ _ NArr NDeq with "[HAwak]").
  by solve_ndisj.
  { iDestruct "HTq" as "(HInv & $ & HEnq & $)". iFrame.
    destruct immediateCancellation eqn:X; first done.
    iApply (dequeue_iterator_update with "[$]"). iPureIntro=> HContra.
    by rewrite X in HContra. }
  iIntros "!>" (?) "[[-> HCancelled]|HSuccess]".
  { rewrite -wp_fupd. destruct immediateCancellation eqn:X=>/=.
    - iDestruct "HCancelled" as (i) "(HCancelled & H↦ & HIsRes)".
      iDestruct "H↦" as (ℓ) "H↦".
      iMod (deq_front_at_least_from_iterator_issued with "[$] HIsRes")
        as "[#HDeqFront HIsRes]"; first done.
      iMod (acquire_resumer_resource_from_immediately_cancelled
              with "[$] HDeqFront HCancelled H↦ HIsRes") as "HR";
        first by solve_ndisj.
      by rewrite X.
      wp_pures. iApply ("HΦ" $! 1). iRight; iLeft. by iFrame.
    - wp_pures. iApply ("HΦ" $! 1). iRight. iLeft. by iFrame.
  }
  iDestruct "HSuccess" as (ns s ->) "[HIsRes #H↦~]".
  iMod (deq_front_at_least_from_iterator_issued with "[$] HIsRes")
    as "[#HDeqFront HIsRes]"; first done.
  wp_pures.
  wp_bind (cellPointerCleanPrev _ _). iApply (cellPointerCleanPrev_spec).
  { iDestruct "HTq" as "(_ & $ & _)". iFrame "H↦~". }
  iIntros "_". iNext. wp_pures. iLöb as "IH".
  wp_bind (derefCellPointer _ _). iApply derefCellPointer_spec.
  { iDestruct "HTq" as "(_ & $ & _)". iFrame "H↦~". }
  iIntros "!>" (ℓ) "#H↦". wp_pures. wp_bind (!_)%E.
  iApply (read_cell_value_by_resumer_spec with "[$]").
  iIntros "!>" (?) "[[-> HIsSus]|[[-> HCancelled]|[[-> HRefused]|HInhabited]]]".
  - (* The cell is empty yet. *)
    wp_pures. wp_bind (Snd _).
    iApply (pass_value_to_empty_cell_spec mayBreakCells with "[$]")=> //.
    iIntros "!>" (passingResult) "HPassingResult".
    destruct passingResult; wp_pures.
    2: { iDestruct "HPassingResult" as "(_ & HIsRes & HV)".
         iApply ("IH" with "HV HCB HΦ HIsRes"). }
    destruct mayBreakCells.
    2: { wp_pures. iApply ("HΦ" $! 0). iLeft. by iFrame. }
    iDestruct "HPassingResult" as "[HCellBreakingToken #HFilled]".
    wp_pures. iClear "IH".
    (* waiting for a suspender to arrive. *)
    iInduction maxWait as [|maxWait'] "IHWait".
    + wp_pures.
      (* the suspender did not manage to arrive while we were waiting. *)
      wp_bind (Snd _). iApply (break_cell_spec with "[$]").
      iIntros "!>" (breakResult) "HBreakResult".
      destruct breakResult; wp_pures.
      * (* breaking succeeded. *)
        iApply ("HΦ" $! 2). iRight; iRight.
        by iDestruct "HBreakResult" as "[$ $]".
      * (* breaking failed as the suspender arrived. *)
        iApply ("HΦ" $! 0). iLeft. by iFrame.
    + wp_pures. wp_bind (!#ℓ)%E.
      awp_apply (check_passed_value false with "HFilled H↦ HCellBreakingToken")
                without "HCB HΦ".
      iDestruct "HTq" as "[HInv _]". iInv "HInv" as (l deqFront) "HOpen".
      iAaccIntro with "HOpen".
      { iIntros "HTq !>". iSplitL; last done. by iExists _, _. }
      iIntros (?) "[HTq HReadValue]". iSplitL "HTq"; first by iExists _, _.
      iIntros "!> [HCB HΦ]".
      destruct (l !! ns) as [[[? res|]|]|]; try iDestruct "HReadValue" as %[].
      destruct res as [[|]|].
      * (* rendezvous succeeded, we may safely leave. *)
        iDestruct "HReadValue" as "[-> HE]". wp_pures.
        iApply ("HΦ" $! 0). iLeft. by iFrame.
      * (* someone else broke the cell? impossible. *)
        by iDestruct "HReadValue" as "[[_ %] _]".
      * (* nothing happened in this cell yet after it was filled. *)
        iDestruct "HReadValue" as "[-> HCellBreakingToken]". wp_pures.
        replace (S maxWait' - 1)%Z with (Z.of_nat maxWait'); last lia.
        iApply ("IHWait" with "HCB HΦ HCellBreakingToken").
  - wp_pures. iApply ("HΦ" $! 1). iRight; iLeft. by iFrame.
  - wp_pures. wp_bind (returnRefusedValue _).
    iApply ("HRefusedValue" with "[$]"). iIntros "!> HE". wp_pures.
    iApply ("HΦ" $! 0). iLeft. by iFrame.
  - iDestruct "HInhabited" as (γf f ->) "[#HTh HFutureCompl]".
    iDestruct (future_is_loc with "[]") as "HLoc". by iDestruct "HTh" as "[$ _]".
    iDestruct "HLoc" as %[fℓ ->]. wp_pures.
    wp_bind (tryCompleteFuture _ _).
    awp_apply (try_resume_cell with "HDeqFront HTq HTh [HV]")
              without "HCB HΦ"=>//.
    iAaccIntro with "HFutureCompl"; first by iIntros "$ !>".
    iIntros (completionResult) "HCompletion !> [HCB HΦ]".
    wp_pures.
    destruct completionResult.
    { (* completion succeeded. *)
      iDestruct "HCompletion" as "(HE & _ & HState)". wp_pures.
      wp_bind (_ <- _)%E. iApply (mark_cell_as_resumed with "[$]").
      iIntros "!> _". wp_pures. iApply ("HΦ" $! 0). iLeft. by iFrame.
    }
    destruct immediateCancellation eqn:X.
    { (* cancellation is immediate. *)
      iDestruct "HCompletion" as "[HV HR]". wp_pures.
      iApply ("HΦ" $! 1). iRight. iLeft. by iFrame.
    }
    iDestruct "HCompletion" as "(HV & #HState & HIsRes)".
    destruct waitForResolution.
    { by wp_pures; iApply ("IH" with "HV HCB HΦ HIsRes"). }
    wp_pures. wp_bind (Snd _).
    iApply (pass_value_to_cancelled_cell_spec with "[HIsRes HV]").
    { iFrame "HTq HState H↦ HIsRes HDeqFront HV HTh". by iPureIntro. }
    iIntros "!>" (valuePassingResult) "HValuePassing".
    destruct valuePassingResult.
    { (* the value was successfully passed. *)
      wp_pures. iApply ("HΦ" $! 0). iLeft. by iFrame.
    }
    iDestruct "HValuePassing" as "[HIsRes HV]".
    wp_pures. iApply ("IH" with "HV HCB HΦ HIsRes").
Qed.

Lemma resume_spec (mayBreakCells shouldAdjust waitForResolution: bool)
      (returnRefusedValue: val) (maxWait: nat) γa γtq γe γd e d v:
  NTq ## NFuture ->
  lit_is_unboxed v ->
  shouldAdjust = negb immediateCancellation ->
  {{{ ERefuse ∗ V v }}}
    returnRefusedValue #v
  {{{ RET #(); ▷ E }}} -∗
  {{{ is_thread_queue γa γtq γe γd e d ∗ awakening_permit γtq ∗
      V v ∗ if mayBreakCells then CB else True }}}
    resume array_interface #maxWait #shouldAdjust #mayBreakCells #waitForResolution
      d returnRefusedValue #v
  {{{ (r: bool), RET #r; if r then E ∗ if mayBreakCells then CB else True
                      else ⌜immediateCancellation ∨ mayBreakCells⌝ ∧
                           R ∗ V v }}}.
Proof.
  iIntros (HMask HLitUnboxed HAdjust) "#HRefusedValue".
  iIntros "!>" (Φ) "[#HTq H] HΦ". wp_lam. wp_pures. iLöb as "IH".
  wp_bind (tryResume _ _ _ _ _ _ _ _).
  iApply (tryResume_spec with "HRefusedValue [H]")=> //. by iFrame.
  iIntros "!>" (n) "Hn". wp_pures.
  iDestruct "Hn" as "[[-> HE]|[[-> H]|[[-> #HMayBreak] H]]]"; wp_pures.
  by iApply "HΦ".
  - rewrite HAdjust. destruct immediateCancellation; wp_pures.
    + iApply "HΦ". iDestruct "H" as "($ & _ & $)". by iLeft.
    + iApply ("IH" with "[H] HΦ"). iDestruct "H" as "($ & $ & $)".
  - iApply "HΦ". iDestruct "HMayBreak" as %HMayBreak. iFrame. by iRight.
Qed.

Definition is_thread_queue_future γtq γa γf (v: val): iProp :=
  ∃ f, is_future NFuture V' γf f ∗
    (⌜v = (f, #())%V⌝ ∧ inv NTq (future_cancellation_permit γf (1/2)%Qp)
      ∗ ∃ x, future_is_completed γf x) ∨
    (∃ i s, ⌜v = (f, s)%V⌝ ∧ rendezvous_thread_handle γtq γf f i
            ∗ is_infinite_array_cell_pointer _ _ array_spec NArr γa s i).

Global Instance is_thread_queue_future_persistent:
  Persistent (is_thread_queue_future γtq γa γf v).
Proof. apply _. Qed.

Definition thread_queue_future_cancellation_permit γf :=
  future_cancellation_permit γf (1/2)%Qp.

Theorem fillThreadQueueFuture_spec γtq γa (v: val):
  {{{ ▷ V' v }}}
    fillThreadQueueFuture v
  {{{ γf v', RET v'; is_thread_queue_future γtq γa γf v' ∗
                     thread_queue_future_cancellation_permit γf ∗
                     future_is_completed γf v }}}.
Proof.
  iIntros (Φ) "HV HΦ". wp_lam. wp_bind (completeFuture _).
  iApply (completeFuture_spec with "HV").
  iIntros "!>" (γf v') "(HFuture & #HCompleted & HPermit)". rewrite -wp_fupd.
  iEval (rewrite -Qp_half_half future_cancellation_permit_Fractional)
    in "HPermit".
  iDestruct "HPermit" as "[HFCanc HFCancInv]".
  iMod (inv_alloc NTq _ (future_cancellation_permit γf (1 / 2)) with "[HFCancInv]")
    as "HFCancInv"; first done.
  wp_pures. iApply "HΦ". iFrame "HFCanc HCompleted". iExists _. iLeft.
  iFrame "HFuture". iSplitR; first done. iFrame "HFCancInv".
  iExists _. by iFrame.
Qed.

Theorem suspend_spec γa γtq γe γd e d:
  {{{ is_thread_queue γa γtq γe γd e d ∗ suspension_permit γtq }}}
    suspend array_interface e
  {{{ v, RET v; ⌜v = NONEV⌝ ∧ E ∗ CB ∨
                ∃ γf v', ⌜v = SOMEV v'⌝ ∧
                         is_thread_queue_future γtq γa γf v' ∗
                         thread_queue_future_cancellation_permit γf }}}.
Proof.
  iIntros (Φ) "[#HTq HIsSus] HΦ". wp_lam. wp_bind (emptyFuture _).
  iApply (emptyFuture_spec with "[% //]").
  iIntros "!>" (γf f) "(#HIsFuture & HCancPermit & HComplPermit)".
  wp_pures. wp_bind (iteratorStep _ _). iApply (iteratorStep_spec with "[HIsSus]").
  2: { by iDestruct "HTq" as "(_ & $ & $ & _)". }
  by solve_ndisj.
  iIntros "!>" (n ns s) "HEnqResult". destruct (decide (ns = n)) as [->|HContra].
  2: { (* someone else cancelled our cell, but it's impossible. *)
    iDestruct "HEnqResult" as "(% & HIsSus & _ & #HCancelled)".
    iDestruct ("HCancelled" $! n with "[%]") as "[HNCancelled H↦]"; first lia.
    iDestruct "H↦" as (ℓ) "H↦". iDestruct "HTq" as "[HInv _]". rewrite -fupd_wp.
    iInv "HInv" as (? ?) "HOpen" "HClose".
    iMod (cell_cancelled_means_present with "HNCancelled H↦ HOpen") as "[HOpen >HPure]".
    by solve_ndisj.
    iDestruct "HPure" as %(c & HEl & HState).
    assert (∃ γf' f' d, l !! n = Some (Some (cellInhabited γf' f' d)))
      as (? & ? & ? & HEl'); simplify_eq.
    { simpl in *. destruct c. by destruct immediateCancellation.
      by eauto. }
    iDestruct "HOpen" as "(_ & HRRs & _)".
    iDestruct (big_sepL_lookup with "HRRs") as "HRR"; first done.
    simpl. iDestruct "HRR" as "[>HC _]".
    by iDestruct (iterator_issued_exclusive with "HIsSus HC") as %[].
  }
  wp_pures. iDestruct "HEnqResult" as "(_ & HIsSus & #H↦~ & _)".
  wp_bind (derefCellPointer _ _). iApply (derefCellPointer_spec with "[]").
  { iDestruct "HTq" as "(_ & $ & _)". done. }
  iIntros "!>" (ℓ) "#H↦". wp_pures. wp_bind (Snd _).
  iApply (inhabit_cell_spec with "[$]"). iIntros "!>" (inhabitResult) "HResult".
  destruct inhabitResult.
  { (* the cell was successfully inhabited. *)
    wp_pures. iApply "HΦ". iRight. iExists _, _. iSplitR; first done.
    iDestruct "HResult" as "[HTh $]". rewrite /is_thread_queue_future.
    iExists _. iRight. iExists _, _. iFrame "HTh". by iSplitR.
  }
  (* the cell is already filled. *)
  wp_pures. wp_bind (!_)%E.
  iDestruct "HResult" as "(#HFilled & HIsSus & HFCompl & HFCanc)".
  iDestruct "HFilled" as (v) "HFilled".
  awp_apply (check_passed_value true with "HFilled H↦ HIsSus")
            without "HΦ HFCompl HFCanc".
  iDestruct "HTq" as "(HInv & HRest)". iInv "HInv" as (l deqFront) "HOpen".
  iAaccIntro with "HOpen". by iIntros "HOpen !>"; iSplitL; first iExists _, _.
  iIntros (?) "[HTq HReadValue]". iSplitL "HTq"; first by iExists _, _.
  iIntros "!> (HΦ & HFCompl & HFCanc)".
  destruct (l !! n) as [[[? res|]|]|]; try iDestruct "HReadValue" as %[].
  assert (res = Some cellBroken ∨ res ≠ Some cellBroken) as [->|HNeq].
  { destruct res as [[|]|].
    - by right.
    - by left.
    - by right.
  }
  * (* the cell is broken. *)
    iDestruct "HReadValue" as "([-> _] & HE & HCB)".
    wp_pures. iApply "HΦ". iLeft. by iFrame.
  * (* rendezvous succeeded, we may safely leave. *)
    iAssert (⌜x = InjRV v⌝ ∧ iterator_issued γe n)%I with "[HReadValue]" as "[-> HE]".
    { by destruct res as [[|]|]. }
    wp_pures. wp_bind (Snd _). iApply (take_cell_value_spec with "[$]").
    iIntros "!>" (takingResult v') "[-> HTakingResult]".
    destruct takingResult.
    2: { wp_pures. iApply "HΦ". iLeft. by iDestruct "HTakingResult" as "[$ $]". }
    (* successfully took the value. *)
    wp_pures. wp_lam. wp_pures. iDestruct "HTakingResult" as "[HV HR]".
    iAssert (▷ V' (#v'))%I with "[HV HR]" as "HV'".
    { iFrame "HR". iExists _. by iFrame. }
    awp_apply (tryCompleteFuture_spec _ false with "HIsFuture") without "HΦ".
    iAssert ((▷ V' #v' ∨ False) ∗ future_completion_permit γf 1)%I with "[HV' HFCompl]"
      as "HAacc".
    by iFrame "HFCompl"; iLeft.
    iAaccIntro with "HAacc". by iIntros "[[$|%] $]".
    iIntros (completionResult) "HCompletion".
    destruct completionResult.
    2: { (* we hold the cancellation permit, so the future is not cancelled. *)
      iDestruct "HCompletion" as "[HContra _]".
      iDestruct (future_cancellation_permit_implies_not_cancelled
                   with "HFCanc HContra") as %[].
    }
    iEval (rewrite -Qp_half_half future_cancellation_permit_Fractional) in "HFCanc".
    iDestruct "HFCanc" as "[HFCanc HFCancInv]".
    iMod (inv_alloc NTq _ (future_cancellation_permit γf (1 / 2)) with "[HFCancInv]")
      as "HFCancInv"; first done.
    iIntros "!> HΦ". wp_pures. iApply "HΦ". iRight. iExists _, _. iSplitR; first done.
    iFrame "HFCanc". iExists _. iLeft. iFrame "HIsFuture". iSplitR; first done.
    iFrame "HFCancInv". by iExists _.
Qed.

Theorem try_cancel_thread_queue_future γa γtq γe γd e d γf f:
  NTq ## NFuture ->
  is_thread_queue γa γtq γe γd e d -∗
  is_thread_queue_future γtq γa γf f -∗
  <<< ▷ thread_queue_future_cancellation_permit γf >>>
    tryCancelThreadQueueFuture f @ ⊤ ∖ ↑NFuture ∖ ↑NTq
  <<< ∃ (r: bool),
      if r then future_is_cancelled γf ∗
        ∃ i f' s, ⌜f = (f', s)%V⌝
        ∗ is_infinite_array_cell_pointer _ _ array_spec NArr γa s i
        ∗ rendezvous_thread_handle γtq γf f' i ∗
        if immediateCancellation
        then inhabited_rendezvous_state γtq i (Some (Cinr (Cinl (to_agree ()))))
             ∗ ▷ cancellation_handle γa i
        else cancellation_registration_token γtq i
      else
        (∃ v, ▷ future_is_completed γf v) ∗
        thread_queue_future_cancellation_permit γf,
      RET #r >>>.
Proof.
  iIntros (HMask) "#HTq #HFuture". iIntros (Φ) "AU". wp_lam.
  iDestruct "HFuture" as (f') "[HFuture|HFuture]".
  - iDestruct "HFuture" as "(HFuture & -> & HFInv & HCompl)".
    iDestruct "HCompl" as (v) "#HCompl". wp_pures.
    awp_apply (tryCancelFuture_spec with "HFuture").
    iInv "HFInv" as ">HCancPermit".
    iApply (aacc_aupd_commit with "AU"); first done.
    iIntros ">HPermit". rewrite /thread_queue_future_cancellation_permit.
    iCombine "HCancPermit" "HPermit" as "HPermit".
    rewrite -future_cancellation_permit_Fractional Qp_half_half.
    iAaccIntro with "HPermit".
    {
      iIntros "HPermit".
      iEval (rewrite -Qp_half_half future_cancellation_permit_Fractional)
        in "HPermit".
      iDestruct "HPermit" as "[$ $]". by iIntros "!> $".
    }
    iIntros (r) "Hr". destruct r.
    by iDestruct (future_is_completed_not_cancelled with "HCompl Hr") as %[].
    iDestruct "Hr" as "[_ HCancPermit]".
    iEval (rewrite -Qp_half_half future_cancellation_permit_Fractional)
      in "HCancPermit".
    iExists false. iDestruct "HCancPermit" as "[$ $]".
    iSplitL; last by iIntros "!> $". by iExists _.
  - iDestruct "HFuture" as (i' s ->) "[HTh HLoc]". wp_pures.
    awp_apply (try_cancel_cell with "HTq HTh"); first done.
    iApply (aacc_aupd_commit with "AU"); first done. iIntros ">HPermit".
    iAaccIntro with "HPermit". by iIntros "$ !> $".
    iIntros (r) "Hr !>". iExists r. iSplitL; last by iIntros "$ !>".
    destruct r.
    + iDestruct "Hr" as "[$ Hr]". iExists _, _, _. iFrame "HLoc".
      iSplitR; first done. by iFrame.
    + iDestruct "Hr" as "[Hr $]". iDestruct "Hr" as (?) "[_ Hr]".
      by iExists _.
Qed.

Theorem await_thread_future γa γtq γe γd e d γf f:
  NTq ## NFuture ->
  is_thread_queue γa γtq γe γd e d -∗
  is_thread_queue_future γtq γa γf f -∗
  <<< ▷ thread_queue_future_cancellation_permit γf >>>
    awaitThreadQueueFuture f @ ⊤ ∖ ↑NFuture ∖ ↑NTq
  <<< ∃ (v': base_lit), V v' ∗ R ∗ future_is_completed γf #v',
      RET (SOMEV #v') >>>.
Proof.
  iIntros (HMask) "#HTq #HFuture". iIntros (Φ) "AU". wp_lam.
  iDestruct "HFuture" as (f') "[HFuture|HFuture]".
  - iDestruct "HFuture" as "(HFuture & -> & HFInv & HCompl)".
    iDestruct "HCompl" as (v) "#HCompl". wp_pures.
    awp_apply (awaitFuture_spec with "HFuture").
    iInv "HFInv" as ">HCancPermit".
    iApply (aacc_aupd_commit with "AU"); first done.
    iIntros ">HPermit". rewrite /thread_queue_future_cancellation_permit.
    iCombine "HCancPermit" "HPermit" as "HPermit".
    rewrite -future_cancellation_permit_Fractional Qp_half_half.
    iAaccIntro with "HPermit".
    {
      iIntros "HPermit".
      iEval (rewrite -Qp_half_half future_cancellation_permit_Fractional)
        in "HPermit".
      iDestruct "HPermit" as "[$ $]". by iIntros "!> $".
    }
    iIntros (r) "Hr". iDestruct "Hr" as "(HV & HCompl' & HCancPermit)".
    iDestruct "HV" as (v' ->) "[HV HR]". iExists _. iFrame. iIntros "!> $ //".
  - iDestruct "HFuture" as (i' s ->) "[HTh HLoc]". wp_pures.
    awp_apply (await_cell with "HTq HTh"); first done.
    iApply (aacc_aupd_commit with "AU"); first done. iIntros ">HPermit".
    iAaccIntro with "HPermit". by iIntros "$ !> $".
    iIntros (r) "Hr !>". iExists r. iSplitL; last by iIntros "$ !>".
    iFrame.
Qed.

End proof.

Typeclasses Opaque inhabited_rendezvous_state
 filled_rendezvous_state
 cell_breaking_token cancellation_registration_token
 cell_cancelling_token thread_queue_state deq_front_at_least
 rendezvous_thread_locs_state rendezvous_filled_value
 rendezvous_thread_handle rendezvous_initialized suspension_permit
 awakening_permit resources_for_resumer cell_resources cell_enqueued
 thread_queue_invariant is_thread_queue_future.
