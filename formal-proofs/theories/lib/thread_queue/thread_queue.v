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

Definition cancelCell: val :=
  λ: "cellPtr", let: "cell" := derefCellPointer array_interface "cellPtr" in
                if: getAndSet "cell" CANCELLEDV = RESUMEDV
                then #false
                else cancelCell array_interface "cellPtr" ;; #true.

Definition fromSome: val :=
  λ: "this", match: "this" with
               InjL "v" => "undefined"
             | InjR "v" => "v"
             end.

Definition suspend: val :=
  λ: "enqIterator",
  let: "future" := emptyFuture #() in
  let: "cellPtr" := iteratorStep array_interface "enqIterator" in
  let: "cell" := derefCellPointer array_interface "cellPtr" in
  let: "future'" := SOME ("future", "cellPtr") in
  if: CAS "cell" (InjLV #()) (InjL "future")
  then "future'"
  else let: "value" := !"cell" in
       if: !("value" = BROKENV) && CAS "cell" "value" TAKENV
       then tryCompleteFuture "future" (fromSome "value") ;; "future'"
       else NONEV.

Definition tryCancelThreadQueueFuture: val :=
  λ: "handler" "f", let: "future" := Fst "f" in
                    let: "cellPtr" := Snd "f" in
                    if: tryCancelFuture "future"
                    then "handler" (λ: <>, cancelCell "cellPtr")
                    else #false.

Definition tryResume: val :=
  λ: "maxWait" "shouldAdjust" "mayBreakCells" "deqIterator" "value",
  match: iteratorStepOrIncreaseCounter
           array_interface "shouldAdjust" "deqIterator" with
      NONE => #1
    | SOME "cellPtr" =>
      cellPointerCleanPrev array_interface "cellPtr" ;;
      (rec: "loop" <> :=
         let: "cell" := derefCellPointer array_interface "cellPtr" in
         let: "cellState" := !"cell" in
         if: "cellState" = NONEV then
           if: CAS "cell" NONEV (SOME "value") then
             if: "mayBreakCells" then
               if: (rec: "wait" "n" := ("n" = #0) ||
                                       (!"cell" = TAKENV) ||
                                       "wait" ("n" - #1)) "maxWait" ||
                   !(CAS "cell" (SOME "value") BROKENV)
               then #0
               else #2
             else #0
           else "loop" #()
         else if: "cellState" = CANCELLEDV then #1
         else #() (* TODO *)
      ) #()
  end.

Definition resume: val :=
  rec: "resume" "deqIterator" :=
    let: "cellPtr" :=
       (rec: "loop" <> :=
          match: iteratorStepOrIncreaseCounter
                   array_interface #false "deqIterator" with
            SOME "c" => "c"
          | NONE => "loop" #()
       end) #() in
    cellPointerCleanPrev array_interface "cellPtr" ;;
    let: "cell" := derefCellPointer array_interface "cellPtr" in
    let: "p" := getAndSet "cell" RESUMEDV in
    if: "p" = CANCELLEDV
    then "resume" "deqIterator"
    else match: "p" with
        InjL "x" => "x"
      | InjR "x" => "impossible"
    end.

Definition newThreadQueue: val :=
  λ: <>, let: "arr" := newInfiniteArray array_interface #2 in
         let: "hd" := ref "arr" in
         let: "tl" := ref "arr" in
         let: "enqIdx" := ref #0 in
         let: "deqIdx" := ref #0 in
         (("enqIdx", "hd"), ("deqIdx", "tl")).

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

Notation namesR := (agreeR (prodO (prodO gnameO gnameO) gnameO)).
Notation enqueueUR := natUR.
Notation dequeueUR := (prodUR natUR max_natUR).
Notation algebra := (authUR (prodUR (prodUR (prodUR enqueueUR dequeueUR)
                                            (optionUR namesR))
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
      passed_value_resource: base_lit -> iProp;
      cell_breaking_resource: iProp;
    }.

Variable parameters: thread_queue_parameters.
Let E := enqueue_resource parameters.
Let R := dequeue_resource parameters.
Let V := passed_value_resource parameters.
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

Definition deq_front_at_least γtq (n: nat) :=
  own γtq (◯ (ε, (ε, MaxNat n), ε, ε)).

Definition rendezvous_thread_locs_state (γtq γf: gname) (f: val) (i: nat): iProp :=
  rendezvous_state γtq i (Some (Cinr (to_agree (γf, f), None))).

Global Instance rendezvous_thread_locs_state_persistent γtq γt th i:
  Persistent (rendezvous_thread_locs_state γtq γt th i).
Proof. apply _. Qed.

Definition rendezvous_filled_value (γtq: gname) (v: base_lit) (i: nat): iProp :=
  rendezvous_state γtq i (Some (Cinl (to_agree #v, ε))).

Definition V' (v: val): iProp := ∃ (x: base_lit), ⌜v = #x⌝ ∧ V x ∗ R.

Definition rendezvous_thread_handle (γtq γt: gname) th (i: nat): iProp :=
  (is_future NFuture V' γt th ∗ rendezvous_thread_locs_state γtq γt th i)%I.

Global Instance rendezvous_thread_handle_persistent γtq γt th i:
  Persistent (rendezvous_thread_handle γtq γt th i).
Proof. apply _. Qed.

Definition rendezvous_initialized γtq i: iProp :=
  inhabited_rendezvous_state γtq i ε ∨ filled_rendezvous_state γtq i ε.

Definition suspension_permit γ := own γ (◯ (1%nat, ε, ε, ε)).

Definition awakening_permit γ := own γ (◯ (ε, (1%nat, ε), ε, ε)).

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
                ∃ v, ℓ ↦ SOMEV #v ∗ iterator_issued γd i ∗
                       future_completion_permit γf 1%Qp ∗ V v)
           | Some cancellationPrevented =>
             ⌜insideDeqFront⌝ ∧
             cancellation_handle γa i ∗
             (ℓ ↦ InjLV f ∗ E ∗
                (future_completion_permit γf 1%Qp ∨
                 iterator_issued γd i)
              ∨ ℓ ↦ REFUSEDV ∗ resources_for_resumer E γf γd i
              ∨ ∃ v, ℓ ↦ SOMEV #v ∗ iterator_issued γd i ∗
                 future_completion_permit γf 1%Qp ∗ V v)
           | Some (cancellationAllowed d) =>
             match d with
             | None =>
               ℓ ↦ InjLV f ∗ E ∗
               resources_for_resumer (awakening_permit γtq) γf γd i
             | Some (cellTookValue v) =>
               ℓ ↦ SOMEV #v ∗ iterator_issued γd i ∗
                 future_completion_permit γf 1%Qp ∗
                 (cell_cancelling_token γf i ∨ V v)
             | Some cellClosed =>
               ℓ ↦ CANCELLEDV ∗
                 cell_cancelling_token γf i ∗
                 resources_for_resumer (awakening_permit γtq) γf γd i
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

Definition cell_list_contents_auth_ra
           (γa γe γd: gname) l (deqFront: nat): algebra :=
  ● (length l, (deqFront, MaxNat deqFront), Some (to_agree (γa, γe, γd)),
     (map (option_map cellState_ra) l,
      Excl' (count_matching is_nonskippable (drop deqFront l)))).

Lemma rendezvous_state_included γ γa γe γd l deqFront i s:
  own γ (cell_list_contents_auth_ra γa γe γd l deqFront) -∗
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

Lemma rendezvous_state_included' γ γa γe γd l deqFront i s:
  own γ (cell_list_contents_auth_ra γa γe γd l deqFront) -∗
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

Lemma thread_queue_state_valid γtq γa γe γd n l deqFront:
  own γtq (cell_list_contents_auth_ra γa γe γd l deqFront) -∗
  thread_queue_state γtq n -∗
  ⌜n = count_matching is_nonskippable (drop deqFront l)⌝.
Proof.
  iIntros "H● HState".
  iDestruct (own_valid_2 with "H● HState")
    as %[[_ [_ HEq%Excl_included]%prod_included]%prod_included
                                                _]%auth_both_valid.
  by simplify_eq.
Qed.

Theorem cell_list_contents_ra_locs γ γa γe γd l deqFront i γt th:
  own γ (cell_list_contents_auth_ra γa γe γd l deqFront) -∗
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

Theorem cell_enqueued_lookup γtq γa γe γd l i d:
  own γtq (cell_list_contents_auth_ra γa γe γd l d) -∗
  cell_enqueued γtq i -∗
  ⌜exists v, l !! i = Some v⌝.
Proof.
  iIntros "H● HExistsEl".
  iDestruct (rendezvous_state_included with "H● HExistsEl") as %(c & HEl & _).
  iPureIntro. eauto.
Qed.

Definition thread_queue_invariant γa γtq γe γd l deqFront: iProp :=
  own γtq (cell_list_contents_auth_ra γa γe γd l deqFront) ∗
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

Theorem thread_queue_append γtq γa γe γd n l deqFront:
  E -∗ thread_queue_state γtq n -∗
  thread_queue_invariant γa γtq γe γd l deqFront ==∗
  suspension_permit γtq ∗ cell_enqueued γtq (length l) ∗
  thread_queue_state γtq (S n) ∗
  thread_queue_invariant γa γtq γe γd (l ++ [None]) deqFront.
Proof.
  iIntros "HE H◯ (H● & HRRs & HLen & HDeqIdx)".
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
      apply prod_local_update_1, prod_local_update_1=>/=.
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

Global Instance deq_front_at_least_persistent γtq n:
  Persistent (deq_front_at_least γtq n).
Proof. apply _. Qed.

Theorem deq_front_at_least_valid γtq γa γe γd n l deqFront :
  own γtq (cell_list_contents_auth_ra γa γe γd l deqFront) -∗
  deq_front_at_least γtq n -∗
  ⌜n <= deqFront⌝.
Proof.
  iIntros "H● H◯".
  iDestruct (own_valid_2 with "H● H◯") as %[HValid _]%auth_both_valid.
  apply prod_included in HValid. destruct HValid as [HValid _].
  apply prod_included in HValid. destruct HValid as [HValid _].
  apply prod_included in HValid. destruct HValid as [_ HValid].
  apply prod_included in HValid. destruct HValid as [_ HValid].
  apply max_nat_included in HValid. simpl in *.
  iPureIntro; simpl in *; lia.
Qed.

Theorem cell_list_contents__deq_front_at_least i γtq γa γe γd l deqFront:
  (i <= deqFront)%nat ->
  own γtq (cell_list_contents_auth_ra γa γe γd l deqFront) ==∗
  own γtq (cell_list_contents_auth_ra γa γe γd l deqFront) ∗
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
      γtq γa γe γd l deqFront i initialState newState:
  l !! i = Some initialState ->
  is_nonskippable initialState = is_nonskippable newState ->
  (Some (option_map cellState_ra initialState), None) ~l~>
  (Some (option_map cellState_ra newState),
   Some s) ->
  own γtq (cell_list_contents_auth_ra γa γe γd l deqFront) ==∗
  own γtq (cell_list_contents_auth_ra γa γe γd (<[i := newState]> l) deqFront) ∗
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

Lemma inhabit_cell_ra γtq γa γe γd l deqFront i γf f:
  l !! i = Some None ->
  own γtq (cell_list_contents_auth_ra γa γe γd l deqFront) ==∗
  own γtq (cell_list_contents_auth_ra
             γa γe γd (<[i := Some (cellInhabited γf f None)]> l) deqFront) ∗
  rendezvous_thread_locs_state γtq γf f i.
Proof.
  iIntros (HEl) "H●".
  iMod (cell_list_contents_cell_update_alloc with "H●") as "($ & $)"; try done.
  apply option_local_update'''.
  by rewrite None_op_right_id.
  intros n. by rewrite None_op_right_id.
Qed.

Lemma fill_cell_ra γtq γa γe γd l deqFront i v:
  l !! i = Some None ->
  own γtq (cell_list_contents_auth_ra γa γe γd l deqFront) ==∗
  own γtq (cell_list_contents_auth_ra
             γa γe γd (<[i := Some (cellPassedValue v None)]> l) deqFront) ∗
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

Lemma take_cell_value_ra γtq γa γe γd l deqFront i v:
  l !! i = Some (Some (cellPassedValue v None)) ->
  own γtq (cell_list_contents_auth_ra γa γe γd l deqFront) ==∗
  own γtq (cell_list_contents_auth_ra
             γa γe γd (<[i := Some (cellPassedValue v (Some cellRendezvousSucceeded))]> l) deqFront) ∗
  rendezvous_state γtq i (Some (Cinl (to_agree #v, (None, Some (to_agree true))))).
Proof.
  iIntros (HEl) "H●".
  iMod (cell_list_contents_cell_update_alloc with "H●") as "[$ $]"=> //=.
  apply option_local_update'''=> [|n];
    by rewrite -Some_op -Cinl_op -!pair_op None_op_right_id agree_idemp.
Qed.

Lemma break_cell_ra γtq γa γe γd l deqFront i v:
  l !! i = Some (Some (cellPassedValue v None)) ->
  own γtq (cell_list_contents_auth_ra γa γe γd l deqFront) -∗
  cell_breaking_token γtq i ==∗
  own γtq (cell_list_contents_auth_ra
             γa γe γd (<[i := Some (cellPassedValue v (Some cellBroken))]> l) deqFront) ∗
  rendezvous_state γtq i (Some (Cinl (to_agree #v, (None, Some (to_agree false))))).
Proof.
  iIntros (HEl) "H● H◯". iDestruct "H◯" as (?) "H◯".
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
      apply option_local_update, option_local_update, csum_local_update_l.
      apply prod_local_update=> /=; last apply prod_local_update=> /=.
      * apply local_update_total_valid=> _ _. rewrite to_agree_included=> ?.
        by simplify_eq.
      * apply delete_option_local_update. apply _.
      * apply alloc_option_local_update. done.
    + rewrite !list_lookup_singletonM_gt; try lia.
      rewrite list_lookup_insert_ne; last lia.
      done.
  - rewrite !count_matching_is_sum_map -!fmap_is_map !fmap_drop.
    rewrite list_fmap_insert=> /=. rewrite list_insert_id; first done.
    rewrite map_lookup HEl /= //.
Qed.

Lemma awakening_permit_combine γtq n:
  n > 0 ->
  ([∗] replicate n (awakening_permit γtq))%I ≡ own γtq (◯ (ε, (n, ε), ε, ε)).
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
  ([∗] replicate n (suspension_permit γtq))%I ≡ own γtq (◯ (n, ε, ε, ε)).
Proof.
  move=> Hn.
  rewrite big_opL_replicate_irrelevant_element -big_opL_own;
    last by inversion Hn.
  move: (big_opL_op_prodR 0)=> /= HBigOpL.
  rewrite -big_opL_auth_frag !HBigOpL !big_opL_op_ucmra_unit.
  rewrite -big_opL_op_nat' Nat.mul_1_r replicate_length.
  done.
Qed.

Lemma deque_register_ra_update γ γa γe γd l deqFront i n:
  (i + deqFront < length l)%nat ->
  own γ (cell_list_contents_auth_ra γa γe γd l deqFront) -∗
  thread_queue_state γ n ==∗
  own γ (cell_list_contents_auth_ra γa γe γd l (deqFront + S i))
  ∗ [∗] replicate (S i) (awakening_permit γ)
  ∗ thread_queue_state γ
      (n - count_matching is_nonskippable (take (S i) (drop deqFront l)))
  ∗ deq_front_at_least γ (deqFront + S i).
Proof.
  rewrite awakening_permit_combine; last lia.
  iIntros (?) "H● H◯".
  iMod (own_update_2 with "H● H◯") as "($ & $ & $ & $)"; last done.
  apply auth_update, prod_local_update=>/=.
  apply prod_local_update_1, prod_local_update_2, prod_local_update=>/=.
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

Theorem thread_queue_register_for_dequeue γtq γa γe γd l deqFront n:
  ∀ i, find_index is_nonskippable (drop deqFront l) = Some i ->
  ▷ R -∗ ▷ thread_queue_invariant γa γtq γe γd l deqFront -∗
  thread_queue_state γtq n ==∗
  ▷ ([∗] replicate (S i) (awakening_permit γtq)
  ∗ deq_front_at_least γtq (deqFront + S i)
  ∗ thread_queue_invariant γa γtq γe γd l (deqFront + S i)
  ∗ thread_queue_state γtq (n - 1)).
Proof.
  iIntros (i HFindSome) "HR (>H● & HRRs & >HLen & >HDeqIdx) H◯".
  iDestruct "HLen" as %HLen.
  move: (present_cells_in_take_Si_if_next_present_is_Si _ _ _ HFindSome)
    => HPresentCells.
  apply find_index_Some in HFindSome.
  destruct HFindSome as [(v & HEl & HNonSkippable) HRestSkippable].
  rewrite lookup_drop in HEl.
  assert (deqFront + i < length l); first by apply lookup_lt_Some in HEl.
  iMod (deque_register_ra_update with "H● H◯")
    as "($ & $ & H◯ & $)"; first lia.
  rewrite HPresentCells. iFrame "H◯".
  iSplitL "HR HRRs".
  - erewrite <-(take_drop_middle l _ v); last done.
    rewrite !big_sepL_app=>/=.
    iDestruct "HRRs" as "(HInit & H & HTail)".
    apply lookup_lt_Some in HEl. rewrite take_length_le; last lia.
    iSplitL "HInit"; last iSplitR "HTail".
    * iApply (big_sepL_mono with "HInit"). iIntros (k x HEl') "H".
      assert (k < deqFront + i)%nat.
      { apply lookup_lt_Some in HEl'.
        by rewrite take_length_le in HEl'; last lia. }
      iEval (rewrite bool_decide_true; last lia).
      destruct (decide (k < deqFront)).
      + rewrite bool_decide_true; last lia. done.
      + rewrite bool_decide_false; last lia.
        specialize (HRestSkippable (k - deqFront)).
        destruct HRestSkippable as (y & HEl'' & HSkippable); first lia.
        rewrite lookup_drop in HEl''. rewrite lookup_take in HEl'; last lia.
        replace (_ + _) with k in HEl''; last lia. simplify_eq.
        rewrite /cell_resources.
        rewrite /is_nonskippable in HSkippable.
        destruct y as [[|? ? [[| |[[|]|]]|]]|]=> //.
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
  - iPureIntro.
    split; first lia. case. intros _ (v' & HEl' & HNonSkippable').
    replace (_ - _) with (deqFront + i) in HEl' by lia.
    simplify_eq. rewrite /is_nonskippable in HNonSkippable.
    destruct (is_skippable v); contradiction.
Qed.

Lemma awakening_permit_implies_bound γtq γa γe γd l deqFront n:
  own γtq (cell_list_contents_auth_ra γa γe γd l deqFront) -∗
  ([∗] replicate n (awakening_permit γtq)) -∗
  ⌜n <= deqFront⌝.
Proof.
  iIntros "H● HAwaks".
  destruct n; first by iPureIntro; lia.
  rewrite awakening_permit_combine; last lia.
  iDestruct (own_valid_2 with "H● HAwaks")
    as %[[[[_ [HValid%nat_included _]%prod_included]%prod_included
             _]%prod_included _]%prod_included _]%auth_both_valid.
  simpl in *. iPureIntro; lia.
Qed.

Lemma suspension_permit_implies_bound γtq γa γe γd l deqFront n:
  own γtq (cell_list_contents_auth_ra γa γe γd l deqFront) -∗
  ([∗] replicate n (suspension_permit γtq)) -∗
  ⌜n <= length l⌝.
Proof.
  iIntros "H● HSuspends".
  destruct n; first by iPureIntro; lia.
  rewrite suspension_permit_combine; last lia.
  iDestruct (own_valid_2 with "H● HSuspends")
    as %[[[[HValid%nat_included _]%prod_included
             _]%prod_included _]%prod_included _]%auth_both_valid.
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
           ∗ future_completion_permit γf 1%Qp }}}.
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
    2: iDestruct ("HΦ" $! false with "[HCellFilled HFCompl]") as "HΦ";
      first by iFrame; iExists _.
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
           then cell_breaking_token γtq i ∗ rendezvous_filled_value γtq v i
           else E
      else inhabited_rendezvous_state γtq i ε
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
        - iDestruct "HRR" as "($ & $ & HRR)".
          iDestruct "HRR" as "[[Hℓ HRR]|[[Hℓ HRR]|HRR]]".
          + iExists _; iFrame "Hℓ"; iSplitR; first (by iPureIntro).
            iNext; iIntros "Hℓ"; iExists _. iFrame "H↦". iLeft. iFrame.
          + iExists _; iFrame "Hℓ"; iSplitR; first (by iPureIntro).
            iNext; iIntros "Hℓ"; iExists _. iFrame "H↦". iRight. iLeft. iFrame.
          + iDestruct "HRR" as (?) "[Hℓ HRR]".
            iExists _; iFrame "Hℓ"; iSplitR; first (by iPureIntro).
            iNext; iIntros "Hℓ"; iExists _. iFrame "H↦". iRight. iRight.
            iExists _. iFrame.
        - iDestruct "HRR" as "($ & HR' & HRR)".
          iDestruct "HRR" as "[[Hℓ HR]|[>% HR]]".
          + iExists _; iFrame "Hℓ"; iSplitR; first (by iPureIntro).
            iNext; iIntros "Hℓ"; iExists _. iFrame "H↦ HR'". iLeft. iFrame.
          + iDestruct "HR" as (?) "[Hℓ HR]".
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
    2: iSpecialize ("HΦ" $! false with "[H◯]"); first by iExists _, _.
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

Theorem dequeue_iterator_update γa γtq γe γd e d:
  ⊢ is_thread_queue γa γtq γe γd e d -∗
    ⌜¬ immediateCancellation⌝ -∗
    make_laterable (∀ l, ([∗ list] i ∈ l,
    cell_cancelled γa i ∗ (∃ ℓ, cell_location γtq γa i ℓ)
                   ∗ iterator_issued γd i
    ={⊤ ∖ ↑NDeq}=∗ ▷ awakening_permit γtq)).
Proof.
  iIntros "(#HInv & _ & _ & _)" (HCanc).
  iApply (make_laterable_intro True%I); last done.
  iModIntro. iIntros "_". iIntros (cancelledCells).
  iAssert (∀ i ℓ, cell_cancelled γa i ∗ cell_location γtq γa i ℓ ∗
                                 iterator_issued γd i
          ={⊤ ∖ ↑NDeq}=∗ awakening_permit γtq)%I as "HH".
  {
    iIntros (i ℓ) "(#HCellCanc & #H↦ & HIsRes)".
    iInv "HInv" as (l deqFront) "HOpen" "HClose".
    iMod (cell_cancelled_means_present with "HCellCanc H↦ HOpen")
         as "[HOpen >HFact]".
    by solve_ndisj. iDestruct "HFact" as %(c & HEl & HFact).
    iDestruct "HOpen" as "(H● & HRRs & HPures)".
    iDestruct (big_sepL_lookup_acc with "HRRs") as "[HRR HRRsRestore]";
      first done.
    destruct immediateCancellation; first done. simpl in *.
    destruct c as [|? ? [[| |[[c'|]|]]|]]=>//.
    iDestruct "HRR" as "(HIsSus & HTh & HRR)".
    iDestruct "HRR" as (ℓ') "(H↦' & HFutureCancelled & HNotCanc & HRR)".
    destruct c' as [[|]|].
    3: iDestruct "HRR" as "(Hℓ & HE & [[[HFC|[_ HC]] >$]|[_ HC]])".
    2: iDestruct "HRR" as "(Hℓ & HTok & [[[HFC|[_ HC]] >$]|[_ HC]])".
    1: iDestruct "HRR" as "(_ & HC & _)".
    all: try by iDestruct (iterator_issued_exclusive with "HIsRes HC") as ">[]".
    all: iMod ("HClose" with "[-]"); last done.
    all: iExists _, _; iFrame; iApply "HRRsRestore".
    all: iFrame. all: iExists _; iFrame.
  }
  iInduction cancelledCells as [|cancelledCells'] "IH"=>//=.
  iFrame "IH". iIntros "(HCancelled & HLoc & HIsRes)".
  iDestruct "HLoc" as (?) "HLoc". iMod ("HH" with "[-]") as "$"; last done.
  iFrame.
Qed.

Lemma read_cell_value_by_resumer_spec γtq γa γe γd i ptr e d:
  {{{ is_thread_queue γa γtq γe γd e d ∗
      cell_location γtq γa i ptr ∗
      iterator_issued γd i }}}
    !#ptr
  {{{ (v: val), RET v;
      (⌜v = NONEV⌝ ∧ iterator_issued γd i ∨
       ⌜v = CANCELLEDV⌝ ∧ (if immediateCancellation then R
                           else awakening_permit γtq) ∨
       ⌜v = REFUSEDV⌝ ∧ E ∨
       ∃ γf f, ⌜v = InjLV f⌝ ∧ rendezvous_thread_handle γtq γf f i ∗
               future_completion_permit γf (1/2)%Qp)
  }}}.
Proof.
  iIntros (Φ) "(#(HInv & HInfArr & _ & HD) & #H↦ & HIsRes) HΦ".
  iMod (access_iterator_resources with "HD [#]") as "HH"; first done.
  { iApply (own_mono with "HIsRes"). apply auth_included; split=>//=.
    apply prod_included; split; first by apply ucmra_unit_least.
    apply max_nat_included. simpl. done. }
  rewrite awakening_permit_combine; last lia.
  iDestruct "HH" as "[>HH HHRestore]".
  iMod (acquire_cell _ _ _ _ _ _ with "H↦")
    as "[[#>HCellInit|[>Hℓ HCancHandle]] HCloseCell]"; first by solve_ndisj.
  2: { (* Cell was not yet inhabited, so NONEV is written in it. *)
    wp_load. iMod ("HCloseCell" with "[Hℓ HCancHandle]") as "_".
    by iRight; iFrame. iModIntro. iMod ("HHRestore" with "HH").
    iApply "HΦ". by iLeft; iFrame.
  }
  iSpecialize ("HCloseCell" with "[HCellInit]"); first by iLeft.
  iInv "HInv" as (l deqFront) "(>H● & HRRs & >HLen & >HDeqIdx)" "HTqClose".
  iDestruct (own_valid_2 with "H● HH")
    as %[[[[_ [HValid%nat_included _]%prod_included]%prod_included
        _]%prod_included _]%prod_included _]%auth_both_valid.
  simpl in *. iSpecialize ("HHRestore" with "[HH]"); first done.
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
      { iRight. iLeft. destruct immediateCancellation=> //.
        rewrite bool_decide_true; last lia. by iFrame. }
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
      iDestruct "HRR" as "[(Hℓ & HE & [HFutureCompl|HC])|
        [[Hℓ [[[HFutureCompl|[_ HC]] HE]|[_ HC]]]|HRR]]";
        last iDestruct "HRR" as (?) "(_ & HC & _)".
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
        iFrame "H↦". iSplitR; first done. iLeft. iFrame. }
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
        last iDestruct "HRR" as (?) "(_ & HC & _)".
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

(* TRANSITIONS ON CELLS IN THE NON-SUSPENDING CASE *****************************)

Lemma check_passed_value (possibly_async: bool) γtq γa γe γd i (ptr: loc) vf:
  rendezvous_filled_value γtq vf i -∗
  cell_location γtq γa i ptr -∗
  (if possibly_async then True else cell_breaking_token γtq i) -∗
  <<< ∀ l deqFront, ▷ thread_queue_invariant γa γtq γe γd l deqFront >>>
    !#ptr @ ⊤
  <<< ∃ v, thread_queue_invariant γa γtq γe γd l deqFront ∗
           (if possibly_async then True else cell_breaking_token γtq i) ∗
           ⌜match l !! i with
           | Some (Some (cellPassedValue _ d)) =>
             match d with
               | None => v = InjRV #vf
               | Some cellBroken => v = BROKENV
               | Some cellRendezvousSucceeded =>
                 v = TAKENV ∨ possibly_async ∧ v = InjRV #vf
             end
           | _ => False
           end⌝, RET v >>>.
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
    * destruct possibly_async.
      + iSplitL; last iPureIntro.
        { iFrame "H● HLen HDeqIdx". iApply "HRRsRestore".
          iFrame "HIsRes HCancHandle HValUnboxed".
          iExists _. iFrame "H↦". iLeft. iFrame. }
        by split; [|right].
      + iDestruct (cell_breaking_token_exclusive
                     with "HCellBreaking HCellBreaking'") as %[].
    * iFrame "HCellBreaking". iSplitL; last by iPureIntro; left.
      iFrame "H● HLen HDeqIdx". iApply "HRRsRestore".
      iFrame "HIsRes HCancHandle HValUnboxed".
      iExists _. iFrame "H↦". iRight. iFrame.
  - iDestruct "HRR" as "[Hptr HRR]". wp_load.
    iMod ("HClose" with "[-]") as "HΦ"; last by iModIntro.
    iFrame "HCellBreaking". iSplitL; last by iPureIntro.
    iFrame "H● HLen HDeqIdx". iApply "HRRsRestore". iFrame. iExists _. by iFrame.
  - iDestruct "HRR" as "[Hptr HRR]". wp_load.
    iMod ("HClose" with "[-]") as "HΦ"; last by iModIntro.
    iFrame "HCellBreaking". iSplitL; last by iPureIntro; eexists.
    iFrame "H● HLen HDeqIdx". iApply "HRRsRestore". iFrame. iExists _. by iFrame.
Qed.

Lemma break_cell_spec γtq γa γe γd i ptr e d v:
  {{{ is_thread_queue γa γtq γe γd e d ∗
      cell_location γtq γa i ptr ∗
      rendezvous_filled_value γtq v i ∗
      cell_breaking_token γtq i ∗ CB }}}
    CAS #ptr (InjRV #v) BROKENV
  {{{ (r: bool), RET #r; if r then V v ∗ R else E }}}.
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
    wp_cmpxchg_fail. iSpecialize ("HΦ" $! false with "HE").
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
    CAS #ptr (InjRV #v) TAKENV
  {{{ (r: bool), RET #r; if r then V v ∗ R else CB ∗ E }}}.
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
    wp_cmpxchg_suc. iSpecialize ("HΦ" $! true with "[$]").
    iMod ("HTqClose" with "[-HΦ]") as "_"; last by iModIntro; wp_pures.
    iExists _, _. iFrame "H● HDeqIdx". iSplitL; last by iPureIntro.
    iApply "HRRsRestore". iFrame "HIsRes HCancHandle". iSplitR; first done.
    iExists _. iFrame "H↦". iRight. iFrame.
  - (* Cell was broken before we arrived. *)
    iSpecialize ("HRRsRestore" $! _); rewrite list_insert_id //.
    iDestruct "HRR" as "(Hℓ & [[HE HCB]|HContra])".
    2: by iDestruct (iterator_issued_exclusive with "HIsSus HContra") as ">[]".
    wp_cmpxchg_fail. iSpecialize ("HΦ" $! false with "[$]").
    iMod ("HTqClose" with "[-HΦ]") as "_"; last by iModIntro; wp_pures.
    iExists _, _. iFrame "H● HDeqIdx". iSplitL; last by iPureIntro.
    iApply "HRRsRestore". iFrame "HIsRes HCancHandle". iSplitR; first done.
    iExists _. iFrame "H↦". iFrame.
  - (* Cell is still intact, so we may take the value from it. *)
    iDestruct "HRR" as "(Hℓ & HE & HV & HR)".
    wp_cmpxchg_suc. iSpecialize ("HΦ" $! true with "[$]").
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

(* TODO: *)
(* Establishing deqFront_at_least by iterator_issued *)
(* Cancelling a future *)
(* Resuming a future *)
(* Registering cancellation *)
(* Marking the cell as resumed *)
(* Marking the cell as cancelled *)
(* Marking the cell as refused *)
(* Passing a value in async cancellation mode *)

(* CANCELLING A RENDEZVOUS |||||||||||||||||||||||||||||||||||||||||||||||||*)

Lemma inhabited_cell_is_inhabited γtq i l deqFront:
  own γtq (● cell_list_contents_auth_ra l deqFront) -∗
  inhabitant_token γtq i -∗
  ∃ γt th c,
  ⌜l !! i = Some (Some (cellInhabited γt th c))⌝.
Proof.
  iIntros "HAuth HInhToken". rewrite /cell_list_contents_auth_ra.
  iDestruct (own_valid_2 with "HAuth HInhToken") as
      %[[_ HValid]%prod_included _]%auth_both_valid.
  simpl in *.
  iPureIntro.
  move: HValid. rewrite list_lookup_included. intros HValid.
  specialize (HValid i). move: HValid.
  rewrite map_lookup lookup_app_r.
  all: rewrite replicate_length. 2: done.
  rewrite minus_diag /=.
  destruct (l !! i); simpl.
  2: {
    intros HH. exfalso. revert HH.
    rewrite option_included.
    case; first done. intros (? & ? & ? & HContra & _); done.
  }
  rewrite Some_included_total.
  destruct o as [c|]; simpl in *.
  destruct c as [|? ? cd]; eauto.
  all: intros HH; exfalso; revert HH; clear; intros HH.
  all: repeat (apply prod_included in HH; simpl in *; destruct HH as [HH _]).
  all: move: HH; rewrite option_included; case; try done.
  all: intros (? & ? & _ & HContra & _); done.
Qed.

Lemma inhabited_cell_states E R γa γtq γe γd i l deqFront:
  inhabitant_token γtq i -∗
  cell_list_contents E R γa γtq γe γd l deqFront -∗
  ∃ γt th,
  ⌜l !! i = Some (Some (cellInhabited γt th None)) ∨
   l !! i = Some (Some (cellInhabited γt th (Some cellResumed)))⌝.
Proof.
  iIntros "HInhToken (_ & _ & HAuth & HRRs)".
  iDestruct (inhabited_cell_is_inhabited with "HAuth HInhToken") as
      %(γt & th & c & HEl).
  iExists γt, th.
  iDestruct (big_sepL_lookup with "HRRs") as "HR"; first done. simpl.
  iDestruct "HR" as (?) "(_ & HRs)".
  destruct c as [c|].
  2: by iPureIntro; auto.
  destruct c.
  1: (* Cancelled *) iDestruct "HRs" as "(_ & _ & HInhToken' & _)".
  3: (* Abandoned *) iDestruct "HRs" as "(_ & _ & _ & HInhToken' & _)".
  2: (* Resumed *) by iPureIntro; auto.
  all: iDestruct (inhabitant_token_exclusive with "HInhToken HInhToken'") as %[].
Qed.

Lemma cancel_rendezvous_spec E R γa γtq γe γd l deqFront i j:
  find_index still_present (drop deqFront l) = Some j ->
  inhabitant_token γtq i -∗
  ▷ cell_list_contents E R γa γtq γe γd l deqFront ==∗ ▷ (
  (∃ γt th, ⌜l !! i = Some (Some (cellInhabited γt th None))⌝ ∧
    cell_list_contents E R γa γtq γe γd
      (alter (fun _ => Some (cellInhabited γt th (Some (cellCancelled None)))) i l)
      (if (decide (i < deqFront)%nat) then (deqFront + S j)%nat else deqFront) ∗
    canceller_token γtq i ∗
    rendezvous_cancelled γtq i ∨

    ⌜l !! i = Some (Some (cellInhabited γt th (Some cellResumed)))⌝ ∧
    cell_list_contents E R γa γtq γe γd l (deqFront + S j) ∗
    (∃ (ℓ: loc), cell_location γtq γa i ℓ ∗ ▷ ℓ ↦ RESUMEDV) ∗
    awakening_permit γtq)).
Proof.
  iIntros (HFindIndex) "HInhToken HListContents".
  iDestruct (inhabited_cell_states with "HInhToken HListContents")
    as "#>H".
  iDestruct "H" as %(γt & th & [HEl|HEl]).
  all: simpl.
  2: { (* The cell was resumed, we can only extract the awakening permit. *)
    iDestruct (cell_list_contents_lookup_acc with "HListContents")
              as "[HRR HListContentsRestore]"; first done.
    simpl.
    iDestruct "HRR" as (?) "(#HArrMapsto & #HRendThread & HIsSus & HIsRes &
      HCellCanc & [[HInhToken' _]|(Hℓ & HR & HPerms)])".
    by iDestruct (inhabitant_token_exclusive with "HInhToken HInhToken'") as ">%".
    iDestruct ("HListContentsRestore" with "[-HR Hℓ]") as "HListContents".
    {
      iExists _. iFrame "HIsSus HIsRes HArrMapsto HRendThread HCellCanc".
      iLeft. iFrame "HInhToken". iDestruct "HPerms" as "[[_ HRes]|HNoPerms]".
      all: eauto.
    }
    iExists _, _. iRight. iSplitR; first done.
    iMod (cell_list_contents_register_for_dequeue with "HR HListContents")
      as "(>[$ _] & $ & _)"; first done.
    iExists _. by iFrame.
  }
  (* The cell was inhabited, but not resumed. Cancel it. *)
  iDestruct "HListContents" as
      "(>% & #>HResStage & >HAuth & HRRs)".

  assert (inhabitant_token γtq i ⊣⊢
          inhabitant_token' γtq i (1/2)%Qp ∗
          inhabitant_token' γtq i (1/2)%Qp)%I as Hsplit_inh_token.
  {
    rewrite -own_op -auth_frag_op -pair_op list_singletonM_op ucmra_unit_left_id.
    rewrite -pair_op ucmra_unit_right_id.
    replace (own γtq _) with (inhabitant_token γtq i). done.
    congr (own γtq (◯ (ε, {[ i := (Some _, ε, ε, ε, ε)]}))).
    symmetry. apply Qp_half_half.
  }

  assert ((map cell_state_to_RA l, ε) ~l~>
          (map cell_state_to_RA (alter (fun _ => Some (cellInhabited γt th (Some (cellCancelled None)))) i l),
            {[ i := (ε, cellCancelledO, ε)]}
              ⋅ {[ i := ε]}
          )
          ) as Hupdate_ra_map.
  { move: HEl. clear. intros HInh.
    apply list_lookup_local_update.
    intros j. rewrite lookup_nil map_lookup map_lookup list_singletonM_op.
    destruct (decide (i = j)); first subst.
    {
      rewrite list_lookup_singletonM list_lookup_alter.
      rewrite HInh. simpl.
      apply option_local_update', prod_local_update; simpl; last done.
      apply prod_local_update; simpl; first done.
      by apply max_nat_local_update; simpl; lia.
    }
    destruct (decide (i < j)%nat).
    by rewrite list_lookup_singletonM_gt // list_lookup_alter_ne //.
    rewrite list_lookup_alter_ne // list_lookup_singletonM_lt; last by lia.
    assert (i < length l)%nat. by apply lookup_lt_is_Some; eauto.
    assert (is_Some (l !! j)) as [? ->]. by apply lookup_lt_is_Some; lia.
    by apply option_local_update'.
  }
  iExists _, _. iLeft. iSplitR; first done.

  destruct (decide (i < deqFront)%nat).
  (* The cancellation happened inside the deque front, we need to move it. *)
  {
    iMod (own_update with "HAuth") as "[HAuth [HAwak HDeqFront]]".
    by apply deque_register_ra_update.
    iMod (own_update with "HAuth") as "[HAuth HFrag]".
    apply auth_update_alloc.
    2: iFrame "HAuth".
    {
      apply prod_local_update'; simpl.
      2: by apply Hupdate_ra_map.
      rewrite alter_length. apply prod_local_update_2, prod_local_update_1.
      apply nat_local_update. done.
    }
    iDestruct "HFrag" as "[HCanc _]".

    rewrite Hsplit_inh_token alter_length.
    iDestruct "HInhToken" as "[$ HRRInh]".
    iFrame "HCanc".
    iSplitR.
    {
      iPureIntro.
      assert (deqFront + j < length l)%nat; last lia.
      apply find_index_Some in HFindIndex.
      destruct HFindIndex as [(? & HEl' & _) _].
      rewrite lookup_drop in HEl'.
      apply lookup_lt_is_Some.
      eauto.
    }
    rewrite drop_alter; last by lia.
    iSplitR.
    {
      rewrite -drop_drop. remember (drop deqFront l) as l'.
      replace l' with (take (S j) l' ++ drop (S j) l').
      2: by rewrite take_drop.
      rewrite big_sepL_app. rewrite take_drop.
      by iDestruct "HResStage" as "[_ $]".
    }
    remember (alter _ _ _) as K.
    replace l with (take i l ++ Some (cellInhabited γt th None) :: drop (S i) l).
    2: by rewrite take_drop_middle.
    subst.
    erewrite take_drop_middle_alter; last done.
    rewrite !big_sepL_app /=.
    destruct (deqFront - i)%nat eqn:HDec; first by lia.
    destruct (deqFront + S j - i)%nat eqn:HDec'; first by lia.
    simpl.
    iDestruct "HRRs" as "(HRRsPre & HRR & HRRsPost)".
    iSplitL "HRRsPre"; last iSplitR "HRRsPost".
    - iApply (big_sepL_mono with "HRRsPre"). iIntros (k y HLookup) "Hy".
      admit.
    - admit.
    - admit.
  }
  { (* Otherwise, we're not on the deque front *)
    assert (deqFront <= i)%nat as HSum by lia.
    apply nat_le_sum in HSum. destruct HSum as [z ->].
    iMod (own_update with "HAuth") as "[HAuth HFrag]".
    apply auth_update_alloc.
    2: iFrame "HAuth".
    {
      apply prod_local_update'; simpl.
      2: by apply Hupdate_ra_map.
      rewrite alter_length. apply prod_local_update_2, prod_local_update_1.
      done.
    }
    rewrite alter_length drop_alter'.
    iAssert (rendezvous_cancelled γtq (deqFront + z)) as "#$".
    {
      iApply (own_mono with "HFrag").
      rewrite auth_included /= prod_included /=.
      split; first done. split; first by apply ucmra_unit_least.
      rewrite list_singletonM_op. apply list_singletonM_included.
      rewrite list_lookup_singletonM.
      eexists. split; first done.
      apply prod_included'; split; simpl; last done.
      apply prod_included'; split; simpl; last done.
      done.
    }
    rewrite Hsplit_inh_token. iDestruct "HInhToken" as "[$ HInhToken]".
    iSplitR; first by iPureIntro.
    iSplitR.
    {
      repeat rewrite big_sepL_forall.
      iIntros "!> !>" (k x HEl').
      destruct (decide (z = k)).
      {
        subst. rewrite list_lookup_alter in HEl'.
        rewrite lookup_drop HEl in HEl'. simpl in *.
        simplify_eq. done.
      }
      iApply "HResStage". iPureIntro.
      rewrite <-HEl'. by rewrite list_lookup_alter_ne.
    }
    remember (alter _ _ _) as K.
    erewrite <-(take_drop_middle l (deqFront + z)); last done.
    subst. erewrite take_drop_middle_alter; last done.
    rewrite !big_sepL_app.
    iDestruct "HRRs" as "($ & HRR & $)".
    assert (deqFront + z < length l)%nat.
    by apply lookup_lt_is_Some; eauto.
    rewrite Nat.add_0_r take_length_le; last lia.
    simpl.

    iDestruct "HRR" as (ℓ) "HRR". iExists ℓ.
    iDestruct "HRR" as "($ & Hℓ & HNoPerms & HH & $ & $ & $ & $)".
    iFrame "HInhToken". iFrame.
    by rewrite !decide_False; try lia.
  }
Admitted.

Lemma rendezvous_done_from_auth γtq i γt th d l deqFront:
  l !! i = Some (Some d) ->
  (d = cellFilled ∨ d = cellInhabited γt th (Some cellAbandoned) ∨
   d = cellInhabited γt th (Some cellResumed)) ->
  own γtq (● cell_list_contents_auth_ra l deqFront) ==∗
   own γtq (● cell_list_contents_auth_ra l deqFront) ∗ rendezvous_done γtq i d.
Proof.
  iIntros (HEl Hd) "HAuth".
  iMod (own_update with "HAuth") as "[$ $]"; last done.
  apply auth_update_core_id.
  apply _.
  apply prod_included'; split; simpl.
  by apply ucmra_unit_least.
  apply list_lookup_included.
  intros j.
  rewrite map_lookup.
  assert (i < length l)%nat.
  by apply lookup_lt_is_Some; eauto.
  destruct (decide (j < i)%nat).
  {
    rewrite list_lookup_singletonM_lt; last done.
    assert (is_Some (l !! j)) as [? ->].
    by apply lookup_lt_is_Some; lia.
    simpl.
    apply Some_included_total.
    apply ucmra_unit_least.
  }
  destruct (decide (j = i)).
  2: {
    rewrite list_lookup_singletonM_gt; try lia.
    rewrite option_included. left. done.
  }
  subst.
  rewrite HEl.
  rewrite list_lookup_singletonM.
  apply Some_included_total.
  simpl.
  destruct d; first done. destruct Hd as [|[|]]; simplify_eq;
  (apply prod_included; simpl; split; last done);
  (apply prod_included'; simpl; split; last done);
  apply ucmra_unit_least.
Qed.

Lemma do_cancel_rendezvous_spec E R γa γtq γe γd e d l deqFront i j:
  find_index still_present (drop deqFront l) = Some j ->
  inhabitant_token γtq i -∗
  ▷ is_thread_queue E R γa γtq γe γd e d l deqFront ==∗ ▷ (
  (∃ γt th, ⌜l !! i = Some (Some (cellInhabited γt th None))⌝ ∧
    is_thread_queue E R γa γtq γe γd e d
      (alter (fun _ => Some (cellInhabited γt th (Some (cellCancelled None)))) i l)
      (if (decide (i < deqFront)%nat) then (deqFront + S j)%nat else deqFront) ∗
    canceller_token γtq i ∗
    rendezvous_cancelled γtq i ∨

    ⌜l !! i = Some (Some (cellInhabited γt th (Some cellResumed)))⌝ ∧
    is_thread_queue E R γa γtq γe γd e d l (deqFront + S j)%nat ∗
    (∃ (ℓ: loc), cell_location γtq γa i ℓ ∗ ▷ ℓ ↦ RESUMEDV) ∗
    awakening_permit γtq ∗
    rendezvous_resumed γtq i
  )).
Proof.
  iIntros (HFindIndex) "HInhToken HTq".
  iDestruct "HTq" as "($ & HListContents & #>HDeqFront & HRest)".
  iDestruct (cancel_rendezvous_spec with "HInhToken HListContents") as ">HH";
    first done.
  iDestruct "HH" as (γt th) "[(>HEl & HListContents & HCancTok & HRendCanc)|
    (>HEl & HListContents & HLoc & HAwak)]".
  all: iExists γt, th; iDestruct "HEl" as %HEl.
  {
    iLeft. iFrame "HCancTok HRendCanc HListContents".
    iSplitR; first done.
    iSplitR.
    {
      iDestruct "HDeqFront" as %HDeqFront. iPureIntro.
      destruct (decide (i < deqFront)%nat).
      {
        rewrite list_lookup_alter_ne; last by lia.
        intros [_ (γt' & th' & [? HEl'])].
        apply find_index_Some in HFindIndex.
        destruct HFindIndex as [(v & HEl'' & HPres) _].
        rewrite lookup_drop in HEl''.
        replace (deqFront + S j - 1)%nat with (deqFront + j)%nat in HEl' by lia.
        simplify_eq.
        contradiction.
      }
      {
        destruct (decide (i = deqFront - 1)%nat); try lia.
        rewrite list_lookup_alter_ne //.
      }
    }
    by iFrame.
  }
  {
    iRight.
    iDestruct "HListContents" as "($ & $ & >HLCAuth & $)".
    iMod (rendezvous_done_from_auth with "HLCAuth") as "[$ #HRendRes]"; eauto.
    iFrame "HLoc HAwak".
    iSplitR; first done.
    iSplitL; last by iExists _, _.
    iSplitR.
    {
      iDestruct "HDeqFront" as %HDeqFront. iPureIntro.
      intros [_ (γt' & th' & [? HEl'])].
      apply find_index_Some in HFindIndex.
      destruct HFindIndex as [(v & HEl'' & HPres) _].
      rewrite lookup_drop in HEl''.
      replace (deqFront + S j - 1)%nat with (deqFront + j)%nat in HEl' by lia.
      simplify_eq.
      contradiction.
    }
    by iFrame.
  }
Qed.

(* CANCELLING A RENDEZVOUS /////////////////////////////////////////////////*)

Theorem abandon_rendezvous E R γa γtq γe γd l deqFront i:
  deq_front_at_least γtq (S i) -∗
  inhabitant_token γtq i -∗
  cell_list_contents E R γa γtq γe γd l deqFront ==∗
  (∃ γt th, ⌜l !! i = Some (Some (cellInhabited γt th None))⌝ ∧
  cell_list_contents E R γa γtq γe γd
    (alter (fun _ => Some (cellInhabited γt th (Some cellAbandoned))) i l) deqFront ∗
    rendezvous_abandoned γtq i ∨
  ⌜l !! i = Some (Some (cellInhabited γt th (Some cellResumed)))⌝ ∧
  cell_list_contents E R γa γtq γe γd l deqFront) ∗ R.
Proof.
  iIntros "#HDeqFront HInhToken HListContents".
  rewrite /cell_list_contents.

  iDestruct (inhabited_cell_states with "HInhToken HListContents")
    as (γt th) "#HH".

  iDestruct "HListContents" as (HDfLeLL) "(#HNotDone & HAuth & HEs & HRs & HRRs)".
  iFrame "HNotDone".
  iDestruct (deq_front_at_least__cell_list_contents with "HDeqFront HAuth")
            as %HLb.
  assert (i < length l)%nat as HLt by lia.
  apply lookup_lt_is_Some in HLt. destruct HLt as [v HEl].

  iDestruct "HH" as %[HV|HV].

  2: {
    iDestruct (big_sepL_lookup_acc with "HRRs") as "[HR HRRs]"; first done.
    simpl.
    iDestruct "HR" as (?) "(HArrMapsto & #HRend & HIsRes & HCancHandle & HIsSus & HH)".
    iDestruct "HH" as "[[HInhToken' HPerms]|(Hℓ & HR' & HPerms)]".
    by iDestruct (inhabitant_token_exclusive with "HInhToken HInhToken'") as %[].
    iFrame "HR'".
    iExists γt, th.
    iRight. repeat (iSplitR; first by iPureIntro).
    iFrame.
    iApply "HRRs". iFrame "HRend HIsRes HIsSus HCancHandle".
    iExists _; iFrame "HArrMapsto".
    iLeft.
    by iDestruct "HPerms" as "[[HPerm HResTok]|HNoPerms]"; iFrame.
  }

  replace l with (take i l ++ Some (cellInhabited γt th None) :: drop (S i) l).
  2: by rewrite take_drop_middle.
  rewrite take_app_ge take_length_le; try lia.
  repeat rewrite count_matching_app. repeat rewrite replicate_plus.
  simpl.
  destruct (deqFront - i)%nat eqn:Z; first by lia.
  simpl.
  iDestruct "HRs" as "(HRsHd & $ & HRsTl)".

  iExists γt, th. iLeft.
  repeat rewrite big_sepL_app. simpl. rewrite take_length_le; try lia.
  rewrite -plus_n_O.

  iSplitR.
  { iPureIntro. by rewrite take_drop_middle. }
  rewrite alter_length.

  rewrite take_drop_middle. 2: done.

  erewrite take_drop_middle_alter.
  2: done.
  rewrite take_app_ge take_length_le; try lia.
  repeat rewrite count_matching_app. repeat rewrite replicate_plus.
  rewrite Z.
  repeat rewrite big_sepL_app. simpl.
  iFrame "HRsHd HRsTl".
  iDestruct "HEs" as "($ & HE & $)".
  rewrite take_length_le; try lia.
  iDestruct "HRRs" as "($ & HR & $)".
  rewrite -plus_n_O.
  iFrame "HInhToken".
  iDestruct "HR" as (ℓ) "(HArrMapsto & (Hℓ & HNoPerms & $) & $ & $)".

  iMod (own_update with "HAuth") as "[$ HFrag]".
  2: {
    iSplitR "HFrag".
    2: by iExists _, _; iFrame.
    iSplitR; first done.
    iSplitR.
    2: {
      iExists ℓ. iFrame "HArrMapsto". iSplitR; first by iPureIntro; lia.
      by iRight; iFrame.
    }
    rewrite drop_app_ge take_length_le; try lia.
    rewrite Z. simpl.
    rewrite drop_drop /= plus_n_Sm -Z.
    by replace (i + (deqFront - i))%nat with deqFront by lia.
  }

  apply auth_update_alloc, prod_local_update; simpl.
  {
    apply prod_local_update_1; simpl.
    rewrite app_length /= drop_length take_length_le /=.
    replace (i + S (length l - S i))%nat with (length l).
    done.
    all: lia.
  }

  replace (map cell_state_to_RA l)
  with (map cell_state_to_RA (take i l ++ Some (cellInhabited γt th None) :: drop (S i) l)).
  2: by rewrite take_drop_middle.

  repeat rewrite map_app. simpl.
  remember (map _ _) as K.
  replace i with (length K).
  2: subst; rewrite map_length take_length_le; lia.
  apply list_app_l_local_update.
  clear HeqK.

  remember (map _ _) as K'. clear HeqK'.
  apply list_lookup_local_update; case; simpl.
  2: by intros; rewrite lookup_nil.

  apply option_local_update'.
  apply prod_local_update'.
  2: by apply alloc_option_local_update.
  apply prod_local_update'.
  done.
  apply max_nat_local_update. simpl.
  lia.
Qed.

Theorem try_deque_thread_spec E R γa γtq γe γd (eℓ epℓ dℓ dpℓ: loc):
  ▷ awakening_permit γtq -∗
  <<< ∀ l deqFront, ▷ is_thread_queue E R γa γtq γe γd eℓ epℓ dℓ dpℓ l deqFront >>>
  ((try_deque_thread segment_size) #dpℓ) #dℓ @ ⊤ ∖ ↑N
  <<< ∃ (v: val), ▷ E ∗ (∃ i,
     (⌜l !! i = Some None⌝ ∧ ⌜v = #()⌝ ∧
                     ▷ is_thread_queue E R γa γtq γe γd eℓ epℓ dℓ dpℓ
                            (<[i := Some cellFilled]> l) deqFront) ∗
                            rendezvous_filled γtq i ∨
   ∃ γt (th: loc),
       ▷ rendezvous_thread_handle γtq γt th i ∗ (
      ⌜l !! i = Some (Some (cellInhabited γt th None))⌝ ∧ ⌜v = #th⌝ ∧
      ▷ is_thread_queue E R γa γtq γe γd eℓ epℓ dℓ dpℓ
        (<[i := Some (cellInhabited γt th (Some cellResumed))]> l)
        deqFront ∗ rendezvous_resumed γtq i ∗ resumer_token γtq i ∨

      ⌜l !! i = Some (Some (cellInhabited γt th (Some (cellCancelled None))))⌝ ∗
      rendezvous_cancelled γtq i ∨
      ▷ is_thread_queue E R γa γtq γe γd eℓ epℓ dℓ dpℓ
        (<[i := Some (cellInhabited γt th (Some (cellCancelled (Some cancellationPrevented))))]> l) deqFront ∗
      thread_doesnt_have_permits γt ∨

      (⌜l !! i = Some (Some (cellInhabited γt th (Some (cellCancelled (Some cancellationFinished)))))⌝ ∗
      rendezvous_cancelled γtq i ∨
       ⌜l !! i = Some (Some (cellInhabited γt th (Some cellAbandoned)))⌝ ∗
      rendezvous_abandoned γtq i) ∗
      ⌜v = #th⌝ ∧
      ▷ is_thread_queue E R γa γtq γe γd eℓ epℓ dℓ dpℓ l deqFront ∗
      thread_doesnt_have_permits γt
  )), RET v >>>.
Proof.
  iIntros "HAwaken" (Φ) "AU". iLöb as "IH".
  wp_lam. wp_pures.

  awp_apply (increase_deqIdx with "HAwaken").
  iApply (aacc_aupd_abort with "AU"); first done.
  iIntros (? ?) "HTq".
  iAaccIntro with "HTq".
  by iIntros "$ !> $".
  iIntros (d ?) "($ & HIsRes & #HSegLoc) !> AU !>".

  wp_pures.

  wp_bind (segment_cutoff _).
  iDestruct (iterator_issued_implies_bound with "HIsRes") as "#HDAtLeast".
  awp_apply move_head_forward_spec.
  2: iApply (aacc_aupd_abort with "AU"); first done.
  2: iIntros (? ?) "(HInfArr & HRest)".
  2: iDestruct (is_segment_by_location_prev with "HSegLoc HInfArr")
    as (?) "[HIsSeg HArrRestore]".
  2: iDestruct "HIsSeg" as (?) "HIsSeg".
  2: iAaccIntro with "HIsSeg".
  {
    iApply big_sepL_forall. iIntros (k d' HEl). simpl.
    by iRight.
  }
  {
    iIntros "HIsSeg".
    iDestruct ("HArrRestore" with "HIsSeg") as "$".
    iFrame.
    by iIntros "!> $ !>".
  }
  iIntros "HIsSeg".
  iDestruct ("HArrRestore" with "[HIsSeg]") as "$"; first by iFrame.
  iFrame.
  iIntros "!> AU !>".

  wp_pures.

  awp_apply iterator_move_ptr_forward_spec; try iAssumption.
  {
    iPureIntro.
    move: (Nat.mul_div_le d (Pos.to_nat segment_size)).
    lia.
  }
  iApply (aacc_aupd_abort with "AU"); first done.
  iIntros (? ?) "(HInfArr & HListContents & >% & HRest)".
  iDestruct "HRest" as (? ?) "(HEnqIt & >HDeqIt & HRest)".
  iCombine "HInfArr" "HDeqIt" as "HAacc".
  iAaccIntro with "HAacc".
  {
    iIntros "[$ HDeqIt] !>". iFrame "HListContents".
    iSplitR "HIsRes". iSplitR; first done. iExists _, _. iFrame.
    by iIntros "$ !>".
  }
  iIntros "[$ HDeqPtr] !>".
  iSplitR "HIsRes".
  {
    iFrame "HListContents". iSplitR; first done.
    iExists _, _. iFrame.
  }
  iIntros "AU !>".

  wp_pures. wp_lam. wp_pures.

  replace (Z.rem d (Pos.to_nat segment_size)) with
      (Z.of_nat (d `mod` Pos.to_nat segment_size)).
  2: {
    destruct (Pos.to_nat segment_size) eqn:S; first by lia.
    by rewrite rem_of_nat.
  }
  awp_apply segment_data_at_spec.
  { iPureIntro. apply Nat.mod_upper_bound. lia. }
  iApply (aacc_aupd_abort with "AU"); first done.
  iIntros (? deqFront) "(HInfArr & HRest)".
  iDestruct (is_segment_by_location with "HSegLoc HInfArr")
    as (? ?) "[HIsSeg HArrRestore]".
  iAaccIntro with "HIsSeg".
  {
    iIntros "HIsSeg".
    iDestruct ("HArrRestore" with "HIsSeg") as "$".
    iFrame "HRest".
    by iIntros "!> $ !>".
  }
  iIntros (?) "(HIsSeg & #HArrMapsto & #HCellInv)".
  iDestruct ("HArrRestore" with "[HIsSeg]") as "$"; first done.
  iDestruct "HRest" as "((HLen & HRes & >HAuth & HRest') & HRest)".
  iMod (own_update with "HAuth") as "[HAuth HFrag']".
  2: iAssert (deq_front_at_least γtq deqFront) with "HFrag'" as "HFrag".
  {
    apply auth_update_core_id.
    by repeat (apply pair_core_id; try apply _).
    repeat (apply prod_included'; simpl; split; try apply ucmra_unit_least).
    by apply max_nat_included.
  }
  simpl.
  iAssert (▷ deq_front_at_least γtq (S d))%I as "#HDeqFront".
  {
    iDestruct "HRest" as "(_ & HH)".
    iDestruct "HH" as (? ?) "(_ & [>HDeqCtr _] & _ & _ & >%)".
    iDestruct (iterator_points_to_at_least with "HDAtLeast HDeqCtr") as "%".
    iApply (own_mono with "HFrag").

    apply auth_included. simpl. split; first done.
    repeat (apply prod_included'; simpl; split; try done).
    apply max_nat_included=>/=. lia.
  }
  iFrame.
  iIntros "!> AU !>".

  wp_pures.
  replace (_ + _)%nat with d by (rewrite Nat.mul_comm -Nat.div_mod //; lia).

  awp_apply (resume_rendezvous_spec with "HCellInv HDeqFront HArrMapsto HIsRes").
  iApply (aacc_aupd with "AU"); first done.
  iIntros (? deqFront') "(HInfArr & HCellList & HRest)".
  iAaccIntro with "HCellList".
  by iFrame; iIntros "$ !> $ !>".

  iIntros (?) "[(% & -> & #HRendFilled & HE & HCont)|HH]".
  {
    iRight.
    iExists _.
    iSplitL.
    2: by iIntros "!> HΦ !>"; wp_pures.
    iFrame "HE".
    iExists _.
    iLeft.
    iFrame. iFrame "HRendFilled".
    iSplitR; first done.
    iDestruct "HRest" as "(>% & HRest)".
    iSplitR; first done.
    iSplitR.
    {
      iPureIntro.
      intros (HDeqFront & γt & th & r & HEl).
      destruct (decide (d = (deqFront' - 1)%nat)).
      {
        subst.
        rewrite list_insert_alter in HEl.
        rewrite list_lookup_alter in HEl.
        destruct (_ !! (deqFront' - 1)%nat); simplify_eq.
      }
      rewrite list_lookup_insert_ne in HEl; try done.
      by eauto 10.
    }
    iDestruct "HRest" as (? ?) "HH".
    iExists _, _.
    by rewrite insert_length.
  }

  iDestruct "HH" as (γt th)
    "[(HEl & -> & #HRendRes & HE & HListContents & HResumerToken)|
    [(% & -> & HCanc & #HRend & HNoPerms & HE & HResTok & HListContents)|
    [(% & [-> HAwak] & HListContents)|
    (% & -> & HRendAbandoned & HE & HNoPerms & HListContents)]]]".
  4: { (* Abandoned *)
    iRight.
    iExists _.
    iSplitL.
    2: by iIntros "!> HΦ !>"; wp_pures.
    iFrame "HE".
    iExists _. iRight. iExists γt, th.
    iAssert (▷ rendezvous_thread_handle γtq γt th d)%I with "[-]" as "#HH".
    {
      iDestruct "HListContents" as "(_ & _ & _ & _ & _ & HLc)".
      iDestruct (big_sepL_lookup with "HLc") as "HCR"; first eassumption.
      simpl.
      iDestruct "HCR" as (?) "(_ & $ & _)".
    }
    iFrame "HH".
    iRight. iRight. iRight. iSplitL "HRendAbandoned".
    by iRight; iFrame.
    iSplitR; first by iPureIntro.
    iFrame "HNoPerms".
    by iFrame.
  }
  3: { (* Cancelled and we know about it. *)
    iLeft. iFrame.
    iIntros "!> AU !>". wp_pures.
    iApply ("IH" with "HAwak AU").
  }
  2: { (* Cancelled, but we don't know about it. *)
    iRight. iExists _. iFrame "HE". iSplitL.
    2: by iIntros "!> HΦ !>"; wp_pures.
    iExists _. iRight. iExists _, _. iFrame "HRend".
    iRight. iLeft. by iFrame "HCanc".
  }
  (* Resumed *)
  iRight.
  iDestruct "HEl" as %HEl.
  iExists _. iFrame "HE". iSplitL.
  2: by iIntros "!> HΦ !>"; wp_pures.
  iExists _. iRight. iExists _, _.
  iAssert (▷ rendezvous_thread_handle γtq γt th d)%I with "[-]" as "#HH".
  {
    iDestruct "HListContents" as "(_ & _ & _ & _ & _ & HLc)".
    iDestruct (big_sepL_lookup with "HLc") as "HCR".
    {
      rewrite list_insert_alter. erewrite list_lookup_alter.
      by rewrite HEl.
    }
    simpl.
    iDestruct "HCR" as (?) "(_ & $ & _)".
  }
  iFrame "HH". iClear "HH".
  iLeft.
  repeat (iSplitR; first done).

  iDestruct "HRest" as "(>% & HRest)".
  rewrite /is_thread_queue.
  rewrite insert_length.
  iFrame "HRendRes".
  iFrame.
  iPureIntro.
  intros (HLt & γt' & th' & r & HEl'').
  destruct (decide (d = (deqFront' - 1)%nat)).
  {
    subst. erewrite list_insert_alter in HEl''.
    rewrite list_lookup_alter in HEl''.
    destruct (_ !! (deqFront' - 1)%nat); simplify_eq.
  }
  rewrite list_lookup_insert_ne in HEl''; try done.
  by eauto 10.
Qed.

Theorem try_enque_thread_spec E R γa γtq γe γd γt (eℓ epℓ dℓ dpℓ: loc) (th: loc):
  is_thread_handle Nth γt #th -∗
  suspension_permit γtq -∗
  thread_doesnt_have_permits γt -∗
  <<< ∀ l deqFront, ▷ is_thread_queue E R γa γtq γe γd eℓ epℓ dℓ dpℓ l deqFront >>>
  ((try_enque_thread segment_size) #th #epℓ) #eℓ @ ⊤ ∖ ↑N
  <<< ∃ (v: val),
      (∃ i (s: loc), ⌜v = SOMEV (#s, #(i `mod` Pos.to_nat segment_size)%nat)⌝ ∧
       ⌜l !! i = Some None⌝ ∧
       segment_location γa (i `div` Pos.to_nat segment_size)%nat s ∗
       rendezvous_thread_handle γtq γt th i ∗
       ▷ is_thread_queue E R γa γtq γe γd eℓ epℓ dℓ dpℓ
         (alter (fun _ => Some (cellInhabited γt th None)) i l) deqFront ∗
         inhabitant_token γtq i) ∨
      (⌜v = NONEV⌝ ∧
       ▷ is_thread_queue E R γa γtq γe γd eℓ epℓ dℓ dpℓ l deqFront ∗
         thread_doesnt_have_permits γt ∗ ▷ R),
    RET v >>>.
Proof.
  iIntros "#HThLoc HSusp HNoPerms" (Φ) "AU". wp_lam. wp_pures.
  wp_lam. wp_pures.

  wp_bind (!_)%E.
  iMod "AU" as (? ?) "[(HInfArr & HListContents & >% & HRest) [HClose _]]".
  iDestruct "HRest" as (? ?) "(>[HEnqCtr HEnqPtr] & >HDeqIt & HRest)".
  iDestruct "HEnqPtr" as (? ? ?) "[#HSegLoc Hepℓ]".
  wp_load.
  iMod (iterator_counter_is_at_least with "HEnqCtr") as "[HEnqCtr #HEnqAtLeast]".
  iMod ("HClose" with "[-HSusp HNoPerms]") as "AU".
  {
    iFrame.
    iSplitR; first by iPureIntro.
    iExists _, _. iFrame.
    iExists _. iSplitR; first by iPureIntro. iExists _. by iFrame.
  }
  iModIntro.

  wp_pures.
  awp_apply iterator_value_faa. iApply (aacc_aupd_abort with "AU"); first done.
  iIntros (cells ?) "(HInfArr & HListContents & >% & HRest)".
  iDestruct "HRest" as (senqIdx ?) "(>HEnqIt & >HDeqIt & HAwaks & >HSusps & >%)".
  iDestruct "HListContents" as "(HLC1 & HLC2 & >HAuth & HLC3)".
  iAssert (⌜(senqIdx < length cells)%nat⌝)%I as %HEnqLtLen.
  {
    rewrite /suspension_permit.
    iAssert (own γtq (◯ (S senqIdx,ε, ε))) with "[HSusp HSusps]" as "HSusp".
    {
      clear.
      iInduction senqIdx as [|enqIdx'] "IH"; first done. simpl.
      iDestruct "HSusps" as "[HSusp' HSusps]".
      change (S (S enqIdx')) with (1 ⋅ S enqIdx')%nat.
      rewrite pair_op_1 pair_op_1 auth_frag_op own_op.
      iFrame.
      iApply ("IH" with "HSusp [HSusps]").
      iClear "IH".
      by rewrite big_opL_irrelevant_element' seq_length.
    }
    iDestruct (own_valid_2 with "HAuth HSusp") as
        %[[[HValid%nat_included _]%prod_included
                                  _]%prod_included _]%auth_both_valid.
    iPureIntro.
    simpl in *.
    lia.
  }
  iMod (own_update with "HAuth") as "[HAuth HFrag]".
  2: iAssert (exists_list_element γtq senqIdx) with "HFrag" as "#HElExists".
  {
    apply auth_update_core_id; first by apply _.
    apply prod_included; simpl; split.
    by apply ucmra_unit_least.
    apply list_lookup_included.
    revert HEnqLtLen.
    clear.
    intros ? i.
    rewrite -fmap_is_map list_lookup_fmap.
    destruct (decide (i >= S senqIdx)%Z).
    {
      remember (cells !! i) as K. clear HeqK.
      rewrite lookup_ge_None_2.
      2: rewrite list_singletonM_length; lia.
      by apply option_included; left.
    }
    assert (i < length cells)%nat as HEl by lia.
    apply lookup_lt_is_Some in HEl.
    destruct HEl as [? ->]. simpl.
    destruct (decide (i = senqIdx)).
    {
      subst. rewrite list_lookup_singletonM.
      apply Some_included_total, ucmra_unit_least.
    }
    assert (forall (A: ucmraT) (i i': nat) (x: A),
                (i' < i)%nat -> list_singletonM i x !! i' = Some (ε: A))
            as HH.
    {
      clear. induction i; intros [|i']; naive_solver auto with lia.
    }
    rewrite HH. 2: lia.
    apply Some_included_total.
    apply ucmra_unit_least.
  }
  iDestruct (iterator_points_to_at_least with "HEnqAtLeast [HEnqIt]") as %HnLtn'.
  by iDestruct "HEnqIt" as "[$ _]".
  iAaccIntro with "HEnqIt".
  {
    iFrame. iIntros "HEnqIt".
    iSplitL. iSplitR; first done. iExists _, _. iFrame. done.
    by iIntros "!> $ !>".
  }
  simpl. rewrite Nat.add_1_r union_empty_r_L.
  iIntros "[[HEnqCtr HEnqPtr] HIsSus]".
  iClear "HEnqAtLeast".
  iMod (iterator_counter_is_at_least with "HEnqCtr") as "[HEnqCtr #HEnqAtLeast]".
  iClear "HFrag".
  change (own _ (◯ _)) with (iterator_issued γe senqIdx).
  iFrame.
  iSplitR "HIsSus HNoPerms".
  {
    iSplitR; first done.
    iExists _, _. simpl.
    iAssert ([∗ list] _ ∈ seq O (S senqIdx), suspension_permit γtq)%I
            with "[HSusps HSusp]" as "$".
    {
      simpl. iFrame.
      iApply (big_sepL_forall_2 with "HSusps").
      by repeat rewrite seq_length.
      done.
    }
    iFrame.
    iPureIntro. lia.
  }
  iIntros "!> AU !>".

  wp_pures. rewrite quot_of_nat.
  awp_apply (find_segment_spec with "[] HSegLoc").
  by iApply tq_cell_init.
  iApply (aacc_aupd_abort with "AU"); first done.
  iIntros (? ?) "[HInfArr HRest]".
  iAaccIntro with "HInfArr".
  {
    iFrame. iIntros "$ !> $ !> //".
  }
  iIntros (segId ?) "(HInfArr & #HInvs & #HSegLoc' & #HRest')".
  iAssert (⌜(senqIdx `div` Pos.to_nat segment_size <= segId)%nat⌝)%I as "%".
  by iDestruct "HRest'" as "[(% & <-)|(% & % & _)]"; iPureIntro; lia.
  iDestruct (big_sepL_lookup _ _ (senqIdx `div` Pos.to_nat segment_size)%nat with "HInvs") as "HInv".
  by apply seq_lookup; lia.
  iDestruct (cell_invariant_by_segment_invariant
               _ _ _ _ (senqIdx `mod` Pos.to_nat segment_size)%nat with "HInv") as "HInv'".
  by apply Nat.mod_upper_bound; lia.
  simpl.
  rewrite Nat.mul_comm -Nat.div_mod; try lia.
  iDestruct "HInv'" as (ℓ) "(HCellInv & >HMapsTo)".
  iFrame.
  iIntros "!> AU !>".

  wp_pures.

  destruct (decide (senqIdx `div` Pos.to_nat segment_size = segId)%nat).
  2: {
    iDestruct "HRest'" as "[[% ->]|HC]".
    {
      exfalso.
      assert (senqIdx `div` Pos.to_nat segment_size < segId)%nat by lia.
      assert ((segId * Pos.to_nat segment_size) `div` Pos.to_nat segment_size <=
              senqIdx `div` Pos.to_nat segment_size)%nat as HContra.
      by apply Nat.div_le_mono; lia.
      rewrite Nat.div_mul in HContra; lia.
    }
    iDestruct "HC" as "(% & % & HCanc)".
    rewrite segments_cancelled__cells_cancelled.
    remember (Pos.to_nat segment_size) as P.
    iAssert (cell_is_cancelled segment_size γa
              (P * senqIdx `div` P + senqIdx `mod` P)%nat) as "HCellCanc".
    {
      rewrite Nat.mul_comm.
      iApply (big_sepL_lookup with "HCanc").
      apply seq_lookup.
      assert (senqIdx `mod` P < P)%nat by (apply Nat.mod_upper_bound; lia).
      destruct (segId - senqIdx `div` P)%nat eqn:Z; try lia.
      simpl.
      lia.
    }
    rewrite -Nat.div_mod; try lia.

    wp_lam. wp_pures. wp_bind (!_)%E. (* Just so I can open an invariant. *)
    iInv N as "[[>HCancHandle _]|>HInit]" "HClose".
    by iDestruct (cell_cancellation_handle'_not_cancelled with "HCancHandle HCellCanc") as %[].
    iMod "AU" as (? ?) "[(_ & (_ & _ & >HAuth & _ & _ & HCellRRs) & _) _]".
    iDestruct (exists_list_element_lookup with "HElExists HAuth") as %[c HEl].
    destruct c as [c|]; simpl.
    2: {
      iDestruct (own_valid_2 with "HAuth HInit") as
          %[[_ HValid]%prod_included _]%auth_both_valid.
      simpl in *.
      exfalso.
      move: HValid. rewrite list_lookup_included. move=> HValid.
      specialize (HValid senqIdx). move: HValid.
      rewrite list_lookup_singletonM map_lookup HEl /= Some_included_total.
      intros HValid.
      apply prod_included in HValid; simpl in *; destruct HValid as [HValid _].
      apply prod_included in HValid; simpl in *; destruct HValid as [_ HValid].
      apply max_nat_included in HValid. simpl in *; lia.
    }
    iDestruct (big_sepL_lookup with "HCellRRs") as "HR".
    done.
    simpl.
    iDestruct "HR" as (?) "[_ HRest]".
    destruct c as [|? ? c].
    {
      iDestruct "HRest" as "(_ & >HCancHandle & _)".
      iDestruct (cell_cancellation_handle'_not_cancelled with "HCancHandle HCellCanc") as %[].
    }
    destruct c; iDestruct "HRest" as "(_ & >HIsSus' & _)".
    all: iDestruct (iterator_issued_exclusive with "HIsSus HIsSus'") as %[].
  }

  subst.
  iClear "HRest' HInvs HSegLoc HInv". clear.

  awp_apply (iterator_move_ptr_forward_spec with "[%] [$] [$]").
  by move: (Nat.mul_div_le senqIdx (Pos.to_nat segment_size)); lia.
  iApply (aacc_aupd_abort with "AU"); first done.
  iIntros (? ?) "(HInfArr & HListContents & HLog1 & HRest)".
  iDestruct "HRest" as (? ?) "(>HEnqIt & >HDeqIt & HAwaks & >HSusps & HLog2)".
  iCombine "HInfArr" "HEnqIt" as "HAacc".
  iAaccIntro with "HAacc".
  {
    iIntros "[$ HEnqIt]". iFrame.
    iSplitL. by iExists _, _; iFrame.
    by iIntros "!> $ !>".
  }
  iIntros "[$ EnqIt]". iFrame.
  iSplitR "HIsSus HNoPerms".
  by iExists _, _; iFrame.
  iIntros "!> AU !>".

  wp_pures. wp_lam. wp_pures.
  replace (Z.rem senqIdx _) with (Z.of_nat (senqIdx `mod` Pos.to_nat segment_size)%nat).
  2: {
    destruct (Pos.to_nat segment_size) eqn:Z; try lia.
    by rewrite rem_of_nat.
  }

  awp_apply segment_data_at_spec.
  { iPureIntro. apply Nat.mod_upper_bound; lia. }
  iApply (aacc_aupd_abort with "AU"); first done.
  iIntros (? ?) "(HInfArr & HRest)".
  iDestruct (is_segment_by_location with "HSegLoc' HInfArr")
    as (? ?) "[HIsSeg HArrRestore]".
  iAaccIntro with "HIsSeg".
  {
    iIntros "HIsSeg !>".
    iDestruct ("HArrRestore" with "HIsSeg") as "$".
    iFrame.
    by iIntros "$ !>".
  }
  iIntros (?) "(HIsSeg & HArrMapsto' & _)".
  iDestruct (array_mapsto'_agree with "HArrMapsto' HMapsTo") as "->".
  iDestruct ("HArrRestore" with "[HIsSeg]") as "$"; first by iFrame.
  iFrame "HRest".
  iIntros "!> AU !>".

  wp_pures.
  awp_apply (inhabit_cell_spec with "[$] HNoPerms HIsSus HElExists HMapsTo HCellInv").
  iApply (aacc_aupd_commit with "AU"); first done.
  iIntros (? deqFront) "(HInfArr & HListContents & HRest)".
  iAaccIntro with "HListContents".
  { iIntros "$"; iFrame. iIntros "!> $ !>". done. }
  iIntros (?) "H".
  iDestruct "H" as "[(% & -> & HInhToken & #HRend & HListContents')|
    (% & -> & HNoPerms & HR & HListContents)]".
  all: iExists _; iSplitL; [|iIntros "!> HΦ !>"; by wp_pures].
  2: {
    iRight. iSplitR; first done. by iFrame.
  }
  iLeft.
  iExists _, _. iSplitR; first done. iSplitR; first done.
  iFrame "HInhToken HSegLoc' HRend".
  iDestruct "HRest" as "(>% & >HRest)".
  rewrite /is_thread_queue.
  rewrite alter_length.
  iFrame "HInfArr HRest HListContents'".
  rewrite /cell_invariant.
  iPureIntro.
  intros (HLt & γt' & th' & r & HEl).
  destruct (decide (senqIdx = (deqFront - 1)%nat)).
  {
    subst. rewrite list_lookup_alter in HEl.
    destruct (_ !! (deqFront - 1)%nat); simpl in *; discriminate.
  }
  rewrite list_lookup_alter_ne in HEl; eauto 10.
Qed.

Theorem new_thread_queue_spec S R:
  {{{ True }}}
    new_thread_queue segment_size #()
  {{{ γa γtq γe γd eℓ epℓ dℓ dpℓ, RET ((#epℓ, #eℓ), (#dpℓ, #dℓ));
      is_thread_queue S R γa γtq γe γd eℓ epℓ dℓ dpℓ [] 0 }}}.
Proof.
  iIntros (Φ) "_ HPost".
  wp_lam.
  iMod (own_alloc (● (GSet (set_seq 0 0), MaxNat 0))) as (γd) "HAuthD".
  { simpl. apply auth_auth_valid, pair_valid; split; done. }
  iMod (own_alloc (● (GSet (set_seq 0 0), MaxNat 0))) as (γe) "HAuthE".
  { simpl. apply auth_auth_valid, pair_valid; split; done. }
  iMod (own_alloc (● (0%nat, (0%nat, MaxNat 0), []))) as (γtq) "HAuth".
  { apply auth_auth_valid, pair_valid; split; try done.
    apply list_lookup_valid; intro. rewrite lookup_nil //. }
  iMod (own_alloc (● [])) as (γa) "HAuthTq".
  { simpl. apply auth_auth_valid, list_lookup_valid. intros i.
    by rewrite lookup_nil. }
  wp_apply (new_infinite_array_spec with "[HAuthTq]").
  by iFrame; iApply (tq_cell_init γtq γd).
  iIntros (ℓ) "[HInfArr #HSegLoc]".
  wp_pures.

  rewrite -wp_fupd.
  wp_alloc eℓ as "Heℓ". wp_alloc dℓ as "Hdℓ".
  wp_alloc epℓ as "Hepℓ". wp_alloc dpℓ as "Hdpℓ".

  wp_pures.
  iApply "HPost".
  rewrite /is_thread_queue /cell_list_contents /cell_list_contents_auth_ra /=.
  iFrame "HInfArr HAuth".
  repeat iSplitR; try done.
  by iPureIntro; lia.

  iExists 0%nat, 0%nat. simpl.
  rewrite /iterator_points_to /iterator_counter.
  iFrame "Hepℓ Hdpℓ HAuthE HAuthD".
  iSplitL "Heℓ".
  {
    iExists 0%nat. simpl.
    iSplitR; first done.
    iExists _; by iFrame.
  }
  iSplitL "Hdℓ".
  {
    iExists 0%nat. simpl.
    iSplitR; first done.
    iExists _; by iFrame.
  }
  eauto.
Qed.

Theorem thread_queue_unpark_spec E R γa γtq γe γd γt (eℓ epℓ dℓ dpℓ: loc) (th: loc) i:
  rendezvous_resumed γtq i -∗
  is_thread_handle Nth γt #th -∗
  rendezvous_thread_locs_state γtq γt th i -∗
  <<< ∀ l deqFront, resumer_token γtq i ∗
                    ▷ is_thread_queue E R γa γtq γe γd eℓ epℓ dℓ dpℓ l deqFront >>>
    unpark #th @ ⊤ ∖ ↑Nth
  <<< ▷ is_thread_queue E R γa γtq γe γd eℓ epℓ dℓ dpℓ l deqFront, RET #() >>>.
Proof.
  iIntros "#HRendRes #HIsThread #HThreadLocs" (Φ) "AU".
  awp_apply (unpark_spec with "HIsThread").
  iApply (aacc_aupd_commit with "AU"); first done.
  iIntros (? ?) "(HResTok & HInfArr & HListContents & HRest')".
  iDestruct "HListContents" as "(HLi1 & HLi2 & >HTqAuth & HLi4 & HLi5 & HCellResources)".

  iDestruct "HRendRes" as (? ?) "HRendRes".

  iDestruct (cell_list_contents_done_agree with "HTqAuth HRendRes")
            as %HEl'.

  iDestruct (cell_list_contents_ra_locs with "HTqAuth HThreadLocs")
            as %[? HEl''].
  simplify_eq.

  iDestruct (big_sepL_lookup_acc with "HCellResources") as "[HRes HRRsRestore]".
  done.
  simpl.
  iAssert (resumer_token γtq i -∗ resumer_token γtq i -∗ False)%I as "HNoResTok".
  {
    iIntros "HResTok HResTok'".
    iDestruct (own_valid_2 with "HResTok HResTok'") as %HH.
    rewrite -auth_frag_op in HH. exfalso. move: HH.
    rewrite auth_frag_valid pair_valid list_singletonM_op list_lookup_valid /=.
    intros [_ HValid]. specialize (HValid i). move: HValid.
    rewrite list_lookup_singletonM.
    intros HValid.
    destruct HValid as [[[_ []] _] _].
  }
  iDestruct "HRes" as (?) "(HArrMapsto & HTH & HIsSus & HIsRes & HCancHandle &
                            HConds)".
  iDestruct "HConds" as "[[HInhTok [HNoPerms|>HResTok']]|
                          [Hℓ [HR [[HE >HResTok']|HNoPerms]]]]";
    try iDestruct ("HNoResTok" with "HResTok HResTok'") as %[].

  all: iAaccIntro with "HNoPerms".
  all: iFrame "HInfArr HLi1 HLi2 HTqAuth HLi4 HLi5 HRest'".
  3: {
    iFrame "HResTok".
    iIntros ">HNoPerms !>". iSplitL; last by iIntros "$".
    iApply ("HRRsRestore" with "[-]").
    iExists _. iFrame.
    iRight; iFrame.
  }
  {
    iFrame "HResTok".
    iIntros ">HNoPerms !>". iSplitL; last by iIntros "$".
    iApply ("HRRsRestore" with "[-]").
    iExists _. iFrame.
  }

  {
    iIntros "HThPerms !>". iSplitL; last by iIntros "$".
    iApply ("HRRsRestore" with "[-]").
    iExists _. iFrame. iLeft. iFrame.
  }

  {
    iIntros "HThPerms !>".
    iSplitL.
    2: iIntros "HΦ"; wp_pures; by iApply "HΦ".
    iApply ("HRRsRestore" with "[-]").
    iExists _. iFrame. iRight. iFrame. iLeft. iFrame.
  }
Qed.

Theorem thread_queue_check_thread_permits_spec E R γa γtq γe γd
        (eℓ epℓ dℓ dpℓ: loc) i γth (threadHandle: loc) s:
  is_thread_handle Nth γth #threadHandle -∗
  segment_location γa (i `div` Pos.to_nat segment_size) s -∗
  rendezvous_thread_handle γtq γth threadHandle i -∗
  <<< ∀ l deqFront, inhabitant_token γtq i ∗
                    ▷ is_thread_queue E R γa γtq γe γd eℓ epℓ dℓ dpℓ l deqFront >>>
    ! #threadHandle @ ⊤ ∖ ↑Nth
  <<< ∃ (r: bool), ▷ is_thread_queue E R γa γtq γe γd eℓ epℓ dℓ dpℓ l deqFront ∗
                  (⌜r = true⌝ ∧ inhabitant_token γtq i
                   ∨ ⌜r = false⌝ ∧ thread_has_permit γth ∗ R), RET #r >>>.
Proof.
  iIntros "#HTh #HSegLoc #HRend" (Φ) "AU".
  iInv "HTh" as (? t) "[>% [Hℓ >HThAuth]]" "HClose". simplify_eq.
  iMod "AU" as (l deqFront) "[[HInhTok HTq] [_ HClose']]".
  iAssert (▷ ⌜∃ c, l !! i ≡ Some (Some (cellInhabited γth _ c))⌝)%I as "#>HI".
  {
    iDestruct "HTq" as "(_ & (_ & _ & >HH' & _) & _)".
    iDestruct "HRend" as "[_ HRend]".
    iApply (cell_list_contents_ra_locs with "HH' HRend").
  }
  iDestruct "HI" as %(r & HEl'); simplify_eq.
  iAssert (▷ ⌜r = None ∨ r = Some cellResumed⌝)%I as "#>HPures".
  {
    iDestruct "HTq" as "(_ & (_ & _ & _ & _ & _ & HH') & _)".
    iDestruct (big_sepL_lookup with "HH'") as "HRes"; first done.
    simpl. iDestruct "HRes" as (?) "[_ HRes]".
    destruct r as [r|]; last by eauto.
    iRight. iDestruct "HRes" as "(_ & _ & HRes)".
    destruct r.
    2: by eauto.
    1: iDestruct "HRes" as "[>HInhTok' _]".
    2: iDestruct "HRes" as "(_ & >HInhTok' & _)".
    all: by iDestruct (inhabitant_token_exclusive with "HInhTok HInhTok'") as %[].
  }
  iDestruct "HPures" as %HPures.
  iDestruct "HTq" as "(HHead & HListContents & HTail)".
  iDestruct (cell_list_contents_lookup_acc with "HListContents")
    as "[HRes HLcRestore]".
  by erewrite HEl'.
  destruct HPures as [HPures|HPures]; subst; simpl.
  {
    iDestruct "HRes" as (?) "(HArrMapsto & (Hℓ' & >HNoPerms & HRend') & HRest')".
    iAssert (⌜t ≡ true⌝)%I as %HH.
    {
      iDestruct (own_valid_2 with "HThAuth HNoPerms")
        as %[[HH%Some_included _]%prod_included _]%auth_both_valid.
      iPureIntro.
      destruct HH as [[? HOk]|HOk].
      - simpl in *. by apply to_agree_inj.
      - apply prod_included in HOk; simpl in *.
        destruct HOk as [_ HOk].
        by apply to_agree_included in HOk.
    }
    simplify_eq.
    wp_load.
    iMod ("HClose'" with "[-Hℓ HThAuth HClose]") as "HΦ".
    {
      iDestruct ("HLcRestore" with "[HArrMapsto Hℓ' HNoPerms HRend' HRest']") as "HLC".
      by iExists _; iFrame.
      iFrame. iLeft. by iFrame.
    }
    iModIntro.
    iMod ("HClose" with "[Hℓ HThAuth]") as "_".
    {
      iExists _, _. by iFrame.
    }
    done.
  }

  iDestruct "HRes" as (ℓ') "(HArrMapsto & HRendHandle & HIsSus & HIsRes &
    HCancHandle & [[>HInhTok' _]|(Hℓ' & HR & [[>HHasPerm HResTok]|>HNoPerms])])".
  by iDestruct (inhabitant_token_exclusive with "HInhTok HInhTok'") as %[].
  {
    iAssert (⌜t ≡ false⌝)%I as %HH.
    {
      iDestruct (own_valid_2 with "HThAuth HHasPerm")
        as %[[HH%Some_included _]%prod_included _]%auth_both_valid.
      iPureIntro.
      destruct HH as [[? HOk]|HOk].
      - simpl in *. by apply to_agree_inj.
      - apply prod_included in HOk; simpl in *.
        destruct HOk as [_ HOk].
        by apply to_agree_included in HOk.
    }
    simplify_eq.
    wp_load.
    iMod ("HClose'" with "[-Hℓ Hℓ' HThAuth HClose]") as "HΦ'".
    {
      iDestruct ("HLcRestore" with "[HArrMapsto HRendHandle HIsSus HIsRes
        HCancHandle HInhTok HResTok]") as "HLC".
      { iExists _. iFrame. iLeft. iFrame "HInhTok". iRight. iFrame "HResTok". }
      iFrame. iRight. by iFrame.
    }
    iModIntro.
    iMod ("HClose" with "[Hℓ HThAuth]") as "_".
    {
      iExists _, _. by iFrame.
    }
    done.
  }
  {
    iAssert (⌜t ≡ true⌝)%I as %HH.
    {
      iDestruct (own_valid_2 with "HThAuth HNoPerms")
        as %[[HH%Some_included _]%prod_included _]%auth_both_valid.
      iPureIntro.
      destruct HH as [[? HOk]|HOk].
      - simpl in *. by apply to_agree_inj.
      - apply prod_included in HOk; simpl in *.
        destruct HOk as [_ HOk].
        by apply to_agree_included in HOk.
    }
    simplify_eq.
    wp_load.
    iMod ("HClose'" with "[-Hℓ HThAuth HClose]") as "HΦ'".
    {
      iDestruct ("HLcRestore" with "[HArrMapsto HRendHandle HIsSus HIsRes
        HCancHandle HR Hℓ' HNoPerms]") as "HLC".
      { iExists _. iFrame. iRight. iFrame "HR Hℓ'". }
      iFrame. iLeft. by iFrame.
    }
    iModIntro.
    iMod ("HClose" with "[Hℓ HThAuth]") as "_".
    {
      iExists _, _. by iFrame.
    }
    done.
  }
Qed.

Theorem cancel_cell_spec (s: loc) (i: nat) E R γa γtq γe γd eℓ epℓ dℓ dpℓ:
  rendezvous_cancelled γtq i -∗
  segment_location γa (i `div` Pos.to_nat segment_size) s -∗
  canceller_token γtq i -∗
  <<< ∀ l deqFront, ▷ is_thread_queue E R γa γtq γe γd eℓ epℓ dℓ dpℓ l deqFront >>>
      cancel_cell segment_size (#s, #(i `mod` Pos.to_nat segment_size)%nat)%V @ ⊤
  <<< ∃ (v: bool), ∃ γt th, if v
        then ⌜l !! i = Some (Some (cellInhabited γt th (Some (cellCancelled None))))⌝ ∧
             ▷ is_thread_queue E R γa γtq γe γd eℓ epℓ dℓ dpℓ
             (<[i := Some (cellInhabited γt th (Some (cellCancelled (Some cancellationFinished))))]> l) deqFront
        else ⌜l !! i = Some (Some (cellInhabited γt th (Some (cellCancelled (Some cancellationPrevented)))))⌝ ∧
             ▷ is_thread_queue E R γa γtq γe γd eℓ epℓ dℓ dpℓ l deqFront ∗
             ▷ awakening_permit γtq, RET #v >>>.
Proof.
  iIntros "#HRendCanc #HSegLoc HCancTok" (Φ) "AU".
  wp_lam. wp_pures. wp_lam. wp_pures.

  awp_apply (segment_data_at_spec) without "HCancTok".
  by iPureIntro; apply Nat.mod_upper_bound; lia.
  iApply (aacc_aupd_abort with "AU"); first done.
  iIntros (l deqFront) "HTq".
  iDestruct "HTq" as "[HInfArr HTail']".
  iDestruct (is_segment_by_location with "HSegLoc HInfArr")
    as (? ?) "[HIsSeg HInfArrRestore]".
  iAaccIntro with "HIsSeg".
  {
    iIntros "HIsSeg".
    iDestruct ("HInfArrRestore" with "HIsSeg") as "HInfArr".
    iIntros "!>". iSplitL; last by iIntros "$".
    by iFrame.
  }
  iIntros (ℓ) "(HIsSeg & #HArrMapsto & #HCellInv)".
  iDestruct (bi.later_wand with "HInfArrRestore HIsSeg") as "$".
  iFrame.
  iIntros "!> AU !> HCancTok". wp_pures.

  awp_apply getAndSet.getAndSet_spec. clear.
  iApply (aacc_aupd with "AU"); first done.
  iIntros (l n) "(HInfArr & HListContents & HTail')".
  iAssert (▷ ⌜∃ γt th r, l !! i = Some (Some (cellInhabited γt th
                              (Some (cellCancelled r))))⌝)%I
          as "#>HEl".
  {
    iDestruct "HListContents" as "(_ & _ & >HAuth & _)".
    iDestruct (own_valid_2 with "HAuth HRendCanc")
      as %[[_ (x' & HLookup & HInc)%list_singletonM_included]%prod_included
                                                             _]%auth_both_valid.
    iPureIntro.
    rewrite map_lookup /= in HLookup.
    destruct (l !! i) as [el|] eqn:HLookup'; simpl in *; simplify_eq.
    apply prod_included in HInc. destruct HInc as [HInc _]. simpl in HInc.
    apply prod_included in HInc. destruct HInc as [_ HInc]. simpl in HInc.
    apply max_nat_included in HInc.
    destruct el as [[|γt th [[r| |]|]]|]; simpl in HInc; try lia.
    by eauto.
  }
  iDestruct "HEl" as %(γt & th & r & HEl).

  iDestruct (cell_list_contents_lookup_acc with "HListContents")
    as "[HRR HListContentsRestore]"; first done.
  simpl.
  iDestruct "HRR" as (ℓ') "(#>HArrMapsto' & HRendHandle & HIsSus & >HInhTok & HH)".
  iDestruct (array_mapsto'_agree with "HArrMapsto' HArrMapsto") as %->.
  assert (⊢ inhabitant_token' γtq i (1/2)%Qp -∗
            inhabitant_token' γtq i (1/2)%Qp -∗
            inhabitant_token' γtq i (1/2)%Qp -∗ False)%I as HNoTwoCanc.
  {
    iIntros "HInhTok1 HInhTok2 HInhTok3".
    iDestruct (own_valid_3 with "HInhTok1 HInhTok2 HInhTok3") as %HValid.
    iPureIntro.
    move: HValid. rewrite -auth_frag_op -pair_op.
    repeat rewrite list_singletonM_op.
    rewrite auth_frag_valid /=. rewrite pair_valid.
    rewrite list_singletonM_valid. intros [_ [[[[HPairValid _] _] _] _]].
    by compute.
  }
  destruct r as [[|]|].
  {
    iDestruct "HH" as "[> HCancTok' _]".
    by iDestruct (HNoTwoCanc with "HInhTok HCancTok HCancTok'") as %[].
  }
  {
    iDestruct "HH" as "[HIsRes [(Hℓ & HCancHandle & HAwak)|(_ & >HCancTok' & _)]]".
    2: by iDestruct (HNoTwoCanc with "HInhTok HCancTok HCancTok'") as %[].
    iAssert (▷ ℓ ↦ RESUMEDV ∧ ⌜val_is_unboxed RESUMEDV⌝)%I with "[$]" as "HAacc".
    iAaccIntro with "HAacc".
    {
      iIntros "[Hℓ _]". iFrame "HCancTok".
      iIntros "!>".
      iSplitL; last by iIntros "$". iFrame.
      iApply "HListContentsRestore".
      iExists _. iFrame "HArrMapsto' HRendHandle HIsSus HInhTok".
      iFrame "HIsRes". iLeft. iFrame.
    }

    iIntros "Hℓ !>". iRight. iExists false.
    iSplitL.
    {
      iExists γt, th. iSplitR; first done. iFrame "HAwak".
      iFrame. iApply "HListContentsRestore".
      iExists _. iFrame "HArrMapsto' HRendHandle HIsSus HInhTok".
      iFrame "HIsRes". iRight. iFrame.
    }
    iIntros "HΦ' !>". wp_pures.
    by iApply "HΦ'".
  }

  iDestruct "HH" as "(Hℓ & HE & HCancHandle & HNoPerms & HAwak)".

  iAssert (▷ ℓ ↦ InjLV #th ∧ ⌜val_is_unboxed (InjLV #th)⌝)%I with "[$]" as "HAacc".

  iAaccIntro with "HAacc".
  {
    iIntros "[Hℓ _]". iFrame "HCancTok".
    iIntros "!>".
    iSplitL; last by iIntros "$ !>".
    iFrame.
    iApply "HListContentsRestore".
    iExists _. iFrame "HArrMapsto' HRendHandle HIsSus HInhTok".
    iFrame.
  }

  iIntros "Hℓ !>".
  iRight. iExists true. iSplitL.
  {
    iExists γt, th. iSplitR; first done.
  }
  iSplitR "HCancHandle".
  {
    iFrame.
    iApply "HListContentsRestore".
    iExists _. iFrame "HArrMapsto' HRendHandle HIsSus HInhTok".
    iFrame.
    iRight. iRight. iFrame. iRight. iFrame.
  }
  iIntros "AU !>". wp_pures.

  awp_apply (segment_cancel_cell_spec with "HSegLoc HCancHandle").
  by apply Nat.mod_upper_bound; lia.

  iApply (aacc_aupd_commit with "AU"); first done.
  iIntros (? ?) "(HInfArr & HTail')".
  iAaccIntro with "HInfArr".
  { iIntros "$ !>". iFrame. iIntros "$ !> //". }
  iIntros (?) "$ !>". iExists true. iFrame.
  iSplitR; first by iRight.
  iIntros "HΦ !>". wp_pures. by iApply "HΦ".
Qed.

End proof.
