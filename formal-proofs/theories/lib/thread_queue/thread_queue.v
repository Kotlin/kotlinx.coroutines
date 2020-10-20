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
| cellValueTaken
| cellBroken.

Inductive cancellationResult :=
| cellTookValue (v: val)
| cellClosed.

Inductive cancellationResolution :=
| cancellationAllowed (result: option cancellationResult)
| cancellationPrevented.

Inductive futureTerminalState :=
| cellResumed (v: val)
| cellImmediatelyCancelled
| cellCancelled (resolution: option cancellationResolution).

Inductive cellState :=
| cellPassedValue (v: val) (resolution: option cellRendezvousResolution)
| cellInhabited (futureName: gname) (futureLoc: val)
                (resolution: option futureTerminalState).

(** User-visible state of the cell **)

Inductive rendezvousState :=
| RendezvousUninitiated
| RendezvousSuspended (γf: gname) (f: val)
| RendezvousFailed
| RendezvousSucceeded.

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
                       (agreeR unitO)))))))).

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
          (optionUR (exclR (listO (leibnizO rendezvousState))))).

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

Definition rendezvousResolution_ra r :=
  match r with
  | None => (Excl' (), None)
  | Some cellValueTaken => (Excl' (), Some (to_agree true))
  | Some cellBroken => (None, Some (to_agree false))
  end.

Definition cancellationResult_ra r :=
  match r with
  | cellTookValue v => Cinl (to_agree v)
  | cellClosed => Cinr (to_agree ())
  end.

Definition cancellationResolution_ra r :=
  match r with
  | cancellationAllowed r => Cinr (option_map cancellationResult_ra r)
  | cancellationPrevented => Cinl (to_agree ())
  end.

Definition futureTerminalState_ra r :=
  match r with
  | cellResumed v =>
    Cinl (to_agree v)
  | cellImmediatelyCancelled => Cinr (Cinl (to_agree ()))
  | cellCancelled r =>
    Cinr (Cinr (option_map cancellationResolution_ra r))
  end.

Definition cellState_ra (state: cellState): cellStateR :=
  match state with
  | cellPassedValue v d => Cinl (to_agree v,
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

Definition cellStateToRendezvousState (state: option cellState) :=
  match state with
  | None => RendezvousUninitiated
  | Some d => match d with
             | cellPassedValue v d =>
               match d with
               | None => RendezvousUninitiated
               | Some cellValueTaken => RendezvousSucceeded
               | Some cellBroken => RendezvousFailed
               end
             | cellInhabited γ f r =>
               match r with
               | None => RendezvousSuspended γ f
               | Some cellImmediatelyCancelled => RendezvousFailed
               | Some (cellResumed v) => RendezvousSucceeded
               | Some (cellCancelled None) => RendezvousSuspended γ f
               | Some (cellCancelled (Some (cancellationAllowed r))) =>
                 match r with
                 | None => RendezvousSuspended γ f
                 | Some (cellTookValue _) => RendezvousSucceeded
                 | Some cellClosed => RendezvousFailed
                 end
               | Some (cellCancelled (Some cancellationPrevented)) =>
                 RendezvousSucceeded
               end
             end
  end.

Definition thread_queue_state γ (l: list rendezvousState) :=
  own γ (◯ (ε, (ε, Excl' (l : list (leibnizO rendezvousState))))).

Definition deq_front_at_least γtq (n: nat) :=
  own γtq (◯ (ε, (ε, MaxNat n), ε, ε)).

Definition rendezvous_thread_locs_state (γtq γf: gname) (f: val) (i: nat): iProp :=
  rendezvous_state γtq i (Some (Cinr (to_agree (γf, f), None))).

Global Instance rendezvous_thread_locs_state_persistent γtq γt th i:
  Persistent (rendezvous_thread_locs_state γtq γt th i).
Proof. apply _. Qed.

Definition rendezvous_thread_handle (γtq γt: gname) th (i: nat): iProp :=
  (is_future NFuture γt th ∗ rendezvous_thread_locs_state γtq γt th i)%I.

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

Record thread_queue_parameters :=
  ThreadQueueParameters
    {
      is_immediate_cancellation: bool;
      enqueue_resource: iProp;
      dequeue_resource: iProp;
      passed_value_resource: val -> iProp;
      cell_breaking_resource: iProp;
    }.

Variable parameters: thread_queue_parameters.
Let E := enqueue_resource parameters.
Let R := dequeue_resource parameters.
Let V := passed_value_resource parameters.
Let CB := cell_breaking_resource parameters.
Let immediateCancellation := is_immediate_cancellation parameters.

Definition cell_resources
           γtq γa γe γd i (k: option cellState) (insideDeqFront: bool):
  iProp :=
  match k with
  | None => E ∗ if insideDeqFront then R else True%I
  | Some (cellPassedValue v d) =>
    iterator_issued γd i ∗
    cancellation_handle γa i ∗
    ∃ ℓ, cell_location γtq γa i ℓ ∗
         match d with
         | None => ℓ ↦ SOMEV v ∗ E ∗ V v ∗ R
         | Some cellValueTaken =>
           ℓ ↦ TAKENV ∗ iterator_issued γe i ∗ (E ∨ cell_breaking_token γtq i)
         | Some cellBroken => ℓ ↦ BROKENV ∗ (E ∗ CB ∨ iterator_issued γe i)
         end
  | Some (cellInhabited γf f r) =>
    iterator_issued γe i ∗ rendezvous_thread_handle γtq γf f i ∗
    ∃ ℓ, cell_location γtq γa i ℓ ∗
         match r with
         | None => ℓ ↦ InjLV f ∗ cancellation_handle γa i ∗
                  E ∗ (if insideDeqFront then R else True) ∗
                  (future_completion_permit γf 1%Qp ∨ iterator_issued γd i)
         | Some (cellResumed v) =>
           (ℓ ↦ InjLV f ∨ ℓ ↦ RESUMEDV) ∗
           iterator_issued γd i ∗
           future_is_completed γf v ∗
           cancellation_handle γa i ∗
           (V v ∗ R ∨ future_cancellation_permit γf 1%Qp)
         | Some cellImmediatelyCancelled =>
           (ℓ ↦ InjLV f ∨ ℓ ↦ CANCELLEDV) ∗
           ⌜immediateCancellation⌝ ∗
           future_is_cancelled γf
         | Some (cellCancelled d) =>
           future_is_cancelled γf ∗
           ⌜¬ immediateCancellation⌝ ∗
           match d with
           | None =>
             (ℓ ↦ InjLV f ∗ E ∗
                (if insideDeqFront then R else True) ∗
                (future_completion_permit γf 1%Qp ∨
                 iterator_issued γd i)
              ∨ ⌜insideDeqFront⌝ ∧
                ∃ v, ℓ ↦ SOMEV v ∗ iterator_issued γd i ∗
                       future_completion_permit γf 1%Qp ∗ V v ∗ R)
           | Some cancellationPrevented =>
             ⌜insideDeqFront⌝ ∧
             (ℓ ↦ InjLV f ∗ E ∗
                (future_completion_permit γf 1%Qp ∨
                 iterator_issued γd i)
              ∨ ℓ ↦ REFUSEDV ∗
                ((future_completion_permit γf 1%Qp ∨
                  iterator_issued γd i) ∗ E ∨
                 future_completion_permit γf 1%Qp ∗
                 iterator_issued γd i)
              ∨ ∃ v, ℓ ↦ SOMEV v ∗ iterator_issued γd i ∗
                 future_completion_permit γf 1%Qp ∗ V v)
           | Some (cancellationAllowed d) =>
             match d with
             | None =>
               ℓ ↦ InjLV f ∗ E ∗
                 (future_completion_permit γf 1%Qp ∨
                  iterator_issued γd i)
             | Some (cellTookValue v) =>
               ℓ ↦ SOMEV v ∗ iterator_issued γd i ∗
                 future_completion_permit γf 1%Qp ∗ V v ∗ R
             | Some cellClosed =>
             ℓ ↦ CANCELLEDV ∗
                 ((future_completion_permit γf 1%Qp ∨
                   iterator_issued γd i) ∗ awakening_permit γtq ∨
                 future_completion_permit γf 1%Qp ∗
                 iterator_issued γd i)
             end
           end
         end
  end.

Definition cell_list_contents_auth_ra
           (γa γe γd: gname) l (deqFront: nat): algebra :=
  ● (length l, (deqFront, MaxNat deqFront), Some (to_agree (γa, γe, γd)),
     (map (option_map cellState_ra) l,
      Excl' (map cellStateToRendezvousState l :
               list (leibnizO rendezvousState)))).

Lemma rendezvous_state_valid γ γa γe γd l deqFront i s:
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

Lemma rendezvous_state_valid' γ γa γe γd l deqFront i s:
  own γ (cell_list_contents_auth_ra γa γe γd l deqFront) -∗
  rendezvous_state γ i (Some s) -∗
  ⌜∃ c, l !! i = Some (Some c) ∧ s ≼ cellState_ra c⌝.
Proof.
  iIntros "H● H◯".
  iDestruct (rendezvous_state_valid with "H● H◯") as %(c & HEl & HInc).
  iPureIntro.
  destruct c as [el|]; last by apply included_None in HInc.
  simpl in *. eexists. split; first done. move: HInc.
  rewrite Some_included.
  case; last done. intros ->.
  destruct el as [v r|γth f r]; simpl.
  + by apply Cinl_included.
  + by apply Cinr_included.
Qed.

Theorem cell_list_contents_ra_locs γ γa γe γd l deqFront i γt th:
  own γ (cell_list_contents_auth_ra γa γe γd l deqFront) -∗
  rendezvous_thread_locs_state γ γt th i -∗
  ⌜exists c, l !! i = Some (Some (cellInhabited γt th c))⌝.
Proof.
  iIntros "H● H◯".
  iDestruct (rendezvous_state_valid' with "H● H◯") as %([|] & HEl & HInc).
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
  iDestruct (rendezvous_state_valid with "H● HExistsEl") as %(c & HEl & _).
  iPureIntro. eauto.
Qed.

Definition is_nonskippable (r: option cellState): bool :=
  match r with
  | Some (cellInhabited
            γt th (Some (cellCancelled (Some (cancellationAllowed _))))) =>
    false
  | _ => true
  end.

Definition thread_queue_invariant γa γtq γe γd l deqFront: iProp :=
  own γtq (cell_list_contents_auth_ra γa γe γd l deqFront) ∗
      ([∗ list] i ↦ e ∈ l, cell_resources γtq γa γe γd i e
                                          (bool_decide (i < deqFront))) ∗
      ⌜deqFront ≤ length l⌝ ∧
  ⌜deqFront > 0 ∧ (∃ r, l !! (deqFront - 1)%nat = Some r ∧ ~ is_nonskippable r)
  -> False⌝.

Definition is_thread_queue γa γtq γe γd e d :=
  (inv NTq (∃ l deqFront, thread_queue_invariant γa γtq γe γd l deqFront) ∗
   is_infinite_array _ _ array_spec NArr γa (rendezvous_initialized γtq) ∗
   is_iterator _ array_spec NArr NEnq γa (suspension_permit γtq) γe e ∗
   is_iterator _ array_spec NArr NDeq γa (awakening_permit γtq) γd d)%I.

(* TODO: Add a new parameter signifying the mode of the structure. *)

Theorem thread_queue_append γtq γa γe γd l l' deqFront:
  E -∗ thread_queue_state γtq l' -∗
  thread_queue_invariant γa γtq γe γd l deqFront ==∗
  suspension_permit γtq ∗ cell_enqueued γtq (length l) ∗
  thread_queue_state γtq (map cellStateToRendezvousState l
                              ++ [RendezvousUninitiated]) ∗
  thread_queue_invariant γa γtq γe γd (l ++ [None]) deqFront.
Proof.
  iIntros "HE H◯ (H● & HRRs & HLen & HDeqIdx)".
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
      rewrite map_app=> /=.
      by apply alloc_option_local_update.
  }
Qed.

Global Instance deq_front_at_least_persistent γtq n:
  Persistent (deq_front_at_least γtq n).
Proof. apply _. Qed.

Theorem deq_front_at_least__cell_list_contents γtq γa γe γd n l deqFront :
  deq_front_at_least γtq n -∗
  own γtq (cell_list_contents_auth_ra γa γe γd l deqFront) -∗
  ⌜n <= deqFront⌝.
Proof.
  iIntros "H◯ H●".
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

Lemma None_op_right_id (A: cmraT) (a: option A): a ⋅ None = a.
Proof. by destruct a. Qed.

Lemma inhabit_cell_ra γtq γa γe γd l l' deqFront i γf f:
  l !! i = Some None ->
  own γtq (cell_list_contents_auth_ra γa γe γd l deqFront) -∗
  thread_queue_state γtq l' ==∗
  own γtq (cell_list_contents_auth_ra
             γa γe γd (<[i := Some (cellInhabited γf f None)]> l) deqFront) ∗
  thread_queue_state γtq
    (<[i := RendezvousSuspended γf f]> (map cellStateToRendezvousState l)) ∗
  inhabited_rendezvous_state γtq i ε.
Proof.
  iIntros (HEl) "H● H◯".
  iMod (own_update_2 with "H● H◯") as "($ & $ & H◯)"; last by iExists _, _.
  apply auth_update. rewrite insert_length.
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
      rewrite map_lookup HEl=> /=.
      apply option_local_update'''.
      by rewrite None_op_right_id.
      intros n. by rewrite None_op_right_id.
    + rewrite list_lookup_singletonM_gt; last lia.
      rewrite list_lookup_insert_ne; last lia.
      done.
  - etransitivity.
    by apply delete_option_local_update, _.
    rewrite -!fmap_is_map list_fmap_insert=> /=.
    by apply alloc_option_local_update.
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

Lemma deque_register_ra_update γ γa γe γd l deqFront i:
  (i + deqFront < length l)%nat ->
  own γ (cell_list_contents_auth_ra γa γe γd l deqFront) ==∗
  own γ (cell_list_contents_auth_ra γa γe γd l (deqFront + S i))
  ∗ [∗] replicate (S i) (awakening_permit γ)
  ∗ deq_front_at_least γ (deqFront + S i).
Proof.
  rewrite awakening_permit_combine; last lia.
  iIntros (?) "H●". iMod (own_update with "H●") as "[$ [$ $]]"; last done.
  apply auth_update_alloc, prod_local_update_1, prod_local_update_1=>/=.
  apply prod_local_update_2, prod_local_update=> /=.
  - rewrite ucmra_unit_right_id. by apply nat_local_update.
  - apply max_nat_local_update; simpl; lia.
Qed.

Theorem thread_queue_register_for_dequeue γtq γa γe γd l deqFront:
  ∀ i, find_index is_nonskippable (drop deqFront l) = Some i ->
  ▷ R -∗ ▷ thread_queue_invariant γa γtq γe γd l deqFront ==∗
  ▷ ([∗] replicate (S i) (awakening_permit γtq)
  ∗ deq_front_at_least γtq (deqFront + S i)
  ∗ thread_queue_invariant γa γtq γe γd l (deqFront + S i)).
Proof.
  iIntros (i HFindSome) "HR (>H● & HRRs & >HLen & >HDeqIdx)".
  iDestruct "HLen" as %HLen.
  apply find_index_Some in HFindSome.
  destruct HFindSome as [(v & HEl & HNonSkippable) HRestSkippable].
  rewrite lookup_drop in HEl.
  assert (deqFront + i < length l); first by apply lookup_lt_Some in HEl.
  iMod (deque_register_ra_update with "H●") as "[$ [$ $]]"; first lia.
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
      + iDestruct "H" as "(_ & _ & H)".
        iDestruct "H" as (?) "H".
        iDestruct "H" as "(_ & _ & _ & >HContra & _)".
        iDestruct "HContra" as %[].
      + iDestruct "H" as "($ & $ & H)". iFrame "HR".
        iDestruct "H" as (?) "H". iExists _.
        iDestruct "H" as "($ & $ & $ & [H|H])".
        by iLeft; iDestruct "H" as "($ & $ & _ & $)".
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
    simplify_eq. contradiction.
Qed.

Lemma awakening_permit_implies_bound γtq γa γe γd l deqFront n:
  ([∗] replicate n (awakening_permit γtq)) -∗
  own γtq (cell_list_contents_auth_ra γa γe γd l deqFront) -∗
  ⌜n <= deqFront⌝.
Proof.
  iIntros "HAwaks H●".
  destruct n; first by iPureIntro; lia.
  rewrite awakening_permit_combine; last lia.
  iDestruct (own_valid_2 with "H● HAwaks")
    as %[[[[_ [HValid%nat_included _]%prod_included]%prod_included
             _]%prod_included _]%prod_included _]%auth_both_valid.
  simpl in *. iPureIntro; lia.
Qed.

Global Instance is_thread_queue_persistent γa γ γe γd e d:
  Persistent (is_thread_queue γa γ γe γd e d).
Proof. apply _. Qed.

Lemma cell_resources_conflict_invariant γtq γa γe γd ℓ i b c q:
  cell_location γtq γa i ℓ -∗
  cell_resources γtq γa γe γd i (Some c) b -∗
  cancellation_handle γa i -∗
  ℓ ↦{q} - -∗
  False.
Proof.
  iIntros "#H↦ HRR HCancHandle Hℓ".
  iDestruct "Hℓ" as (?) "Hℓ".
  destruct c as [? resolution|? ? resolution].
  - simpl. iDestruct "HRR" as "(_ & HCancHandle' & _)".
    iDestruct (cell_cancellation_handle_exclusive
                 with "HCancHandle HCancHandle'") as %[].
  - simpl. iDestruct "HRR" as "(_ & _ & HRR)".
    iDestruct "HRR" as (ℓ') "[H↦' HRR]".
    iDestruct (infinite_array_mapsto_agree with "H↦ H↦'") as "<-".
    iAssert (∀ v, ℓ ↦ v -∗ False)%I with "[Hℓ]" as "HℓContra".
    { iIntros (?) "Hℓ'".
      iDestruct (mapsto_valid_2 with "Hℓ' Hℓ") as %HContra.
      exfalso; move: HContra; rewrite frac_valid'.
      apply Qp_not_plus_q_ge_1. }
    destruct resolution as [resolution|].
    + destruct resolution as [?| |d].
      * iDestruct "HRR" as "(_ & _ & _ & HCancHandle' & _)".
        iDestruct (cell_cancellation_handle_exclusive
                     with "HCancHandle HCancHandle'") as %[].
      * iDestruct "HRR" as "[[Hℓ'|Hℓ'] _]".
        all: iDestruct ("HℓContra" with "Hℓ'") as %[].
      * iDestruct "HRR" as "(_ & _ & HRR)".
        destruct d as [[[[|]|]|]|].
        all: try (iDestruct "HRR" as "(Hℓ' & _)";
          by iDestruct ("HℓContra" with "Hℓ'") as %[]).
        { iDestruct "HRR" as "[_ [[Hℓ _]|[[Hℓ _]|HRR]]]";
            last iDestruct "HRR" as (?) "[Hℓ _]".
          all: by iDestruct ("HℓContra" with "Hℓ") as %[]. }
        { iDestruct "HRR" as "[[Hℓ _]|[_ HRR]]";
            last iDestruct "HRR" as (?) "[Hℓ _]".
          all: by iDestruct ("HℓContra" with "Hℓ") as %[]. }
    + iDestruct "HRR" as "[Hℓ _]".
      iDestruct ("HℓContra" with "Hℓ") as %[].
Qed.

Lemma inhabit_cell_spec γa γtq γe γd γf i ptr f e d:
  is_future NFuture γf f -∗
  cell_enqueued γtq i -∗
  cell_location γtq γa i ptr -∗
  is_thread_queue γa γtq γe γd e d -∗
  iterator_issued γe i -∗
  <<< ∀ l, thread_queue_state γtq l >>>
    CAS #ptr (InjLV #()) (InjLV f) @ ⊤ ∖ ↑N
  <<< ∃ (r: bool),
          if r
          then ⌜l !! i = Some RendezvousUninitiated⌝ ∧
               rendezvous_thread_handle γtq γf f i ∗
               thread_queue_state γtq (<[i := RendezvousSuspended γf f]> l)
          else filled_rendezvous_state γtq i ε ∗
               thread_queue_state γtq l, RET #r >>>.
Proof.
  iIntros "#HF #HExistsEl #H↦ #HTq HEnq" (Φ) "AU". wp_bind (CmpXchg _ _ _).
  iDestruct "HTq" as "(HInv & HInfArr & _ & _)".

  iInv "HInv" as (l' deqFront) "(>H● & HRRs & >HLen & >HDeqIdx)" "HTqClose".
  iMod (acquire_cell _ _ _ _ _ _ with "H↦")
    as "[[#>HCellInit|[>Hℓ HCancHandle]] HCloseCell]"; first by solve_ndisj.
  {
    iSpecialize ("HCloseCell" with "[HCellInit]"); first by iLeft.
    iMod "AU" as (l) "[HState [_ HClose]]".
    iDestruct "HCellInit" as "[HCellInhabited|HCellFilled]".
    - (* cell is inhabited? impossible, we hold the suspender token. *)
      rewrite /inhabited_rendezvous_state.
      iDestruct "HCellInhabited" as (? ?) "HCellInhabited".
      iDestruct (rendezvous_state_valid' with "H● HCellInhabited")
        as %(c & HEl & HInc).
      destruct c; simpl in *.
      { exfalso. move: HInc. rewrite csum_included. case; first done.
        case; by intros (? & ? & ? & ? & ?). }
      iDestruct (big_sepL_lookup with "HRRs") as "HRR"; first done.
      iDestruct "HRR" as "[>HEnq' _]".
      iDestruct (iterator_issued_exclusive with "HEnq HEnq'") as %[].
    - (* cell was filled already, CAS fails. *)
      iDestruct ("HClose" $! false with "[HState HCellFilled]") as "HΦ";
        first by iFrame.
      iDestruct "HCellFilled" as (?) "HCellFilled".
      iDestruct (rendezvous_state_valid' with "H● HCellFilled")
        as %(c & HEl & HInc).
      destruct c as [v' resolution|]; simpl in *.
      2: { exfalso. move: HInc. rewrite csum_included. case; first done.
           case; by intros (? & ? & ? & ? & ?). }
      iDestruct (big_sepL_lookup_acc with "HRRs") as "[HRR HRRsRestore]";
        first done.
      simpl.
      iDestruct "HRR" as "(H1 & H2 & HRR)".
      iDestruct "HRR" as (ℓ) "[H↦' HRR]".
      iDestruct (infinite_array_mapsto_agree with "H↦ H↦'") as "><-".
      destruct resolution as [[|]|].
      all: iDestruct "HRR" as "(Hℓ & HRR)"; wp_cmpxchg_fail.
      all: iMod "HΦ"; iModIntro; iMod "HCloseCell" as "_".
      all: iDestruct ("HRRsRestore" with "[H1 H2 HRR Hℓ]") as "HRRs";
        first by (iFrame; eauto).
      all: iModIntro; iMod ("HTqClose" with "[-HΦ]") as "_";
        first by iExists _, _; iFrame.
      all: iModIntro; wp_pures; iAssumption.
  }
  {
    iDestruct (rendezvous_state_valid with "H● HExistsEl")
      as %(c & HEl & _).
    destruct c as [contra|].
    { (* it could not have been already allocated! *)
      iDestruct (big_sepL_lookup with "HRRs") as "HRR"; first done.
      iDestruct (cell_resources_conflict_invariant with
                     "H↦ HRR HCancHandle [Hℓ]") as ">[]"; first by eauto. }

    (* The cell wasn't in the list, so the resumer has not yet arrived. *)
    iAssert (▷ ptr ↦ InjLV #() ∧ ⌜val_is_unboxed (InjLV #())⌝)%I with "[Hℓ]" as "HAacc".
    by iFrame.

    iMod (fupd_intro_mask' _ ∅) as "HCloseMask". by set_solver.
    iModIntro. iExists _. iFrame "HAacc". iSplit.
    { iFrame. iIntros "[Hℓ _]". iMod "HCloseMask" as "_".
      iMod ("HCloseCell" with "[HCancHandle Hℓ]"); last done.
      iRight; iFrame. }

    iIntros "Hℓ". iMod "HCloseMask" as "_".
    iMod "AU" as (l deqFront) "[(>HLt & >#HNotDone & >HAuth & HCellRRs) [_ HClose]]".
    iDestruct (exists_list_element_lookup with "HExistsEl HAuth") as %[cr HIsSome].
    iDestruct (big_sepL_later with "HCellRRs") as "HCellRRs".
    destruct cr; simpl.
    {
      iDestruct (big_sepL_lookup_acc with "HCellRRs") as "[HCellR _]".
      done.
      iDestruct (cell_resources_conflict_invariant with
                     "HCellR [$] [$]") as ">HH".
      iAssert (▷ ptr ↦ -)%I with "[Hℓ]" as "HH'". eauto.
      iDestruct ("HH" with "HH'") as ">[]".
    }
    iDestruct (big_sepL_lookup_alter i O
                (fun _ => Some (cellInhabited γt th None))) as "HH";
      first done.
    simpl; iSpecialize ("HH" with "HCellRRs").
    iDestruct "HH" as "[HCell HH]".
    remember (alter (fun _ => Some (cellInhabited γt th None)) i l) as l'.
    assert (length l = length l') as HSameLength.
    { subst. by rewrite alter_length. }
    iMod (own_update _ _ ((● cell_list_contents_auth_ra
          l' deqFront
          ⋅ ◯ (ε, {[i := (Some 1%Qp, Some (to_agree (γt, th)), ε, MaxNat 2, None)]}
              ))
                         ) with "HAuth") as "[HAuth HFrag]".
    { simpl. apply auth_update_alloc.
      rewrite /cell_list_contents_auth_ra.
      rewrite HSameLength. apply prod_local_update_2. subst.
      rewrite -list_insert_alter -!fmap_is_map list_fmap_insert.
      move: HIsSome. clear=> HIsSome.

      apply list_lookup_local_update. revert i HIsSome.
      induction l; first done; intros i HIsSome i'.
      destruct i; simpl in *.
      { simplify_eq. destruct i'; simpl in *; last done. clear.
        apply local_update_unital_discrete. intros z. rewrite None_op_left_id.
        intros _ <-. split; first done.
        rewrite -Some_op. done. }
      destruct i'; simpl.
      { apply local_update_unital_discrete. intros z. rewrite None_op_left_id.
        intros HValid <-. split; first done.
        by rewrite -Some_op ucmra_unit_left_id. }
      apply IHl; assumption.
    }
    iAssert (rendezvous_thread_locs_state γtq γt th i)
      as "#HRendThread".
    {
      iApply (own_mono with "HFrag").
      apply auth_included. simpl; split; try done.
      apply prod_included. simpl; split; try done.
      apply list_lookup_included. clear.
      induction i; case; simpl; try done.
      apply Some_included_total. apply prod_included.
      split; try done. simpl.
      apply prod_included'. simpl. split.
      2: by apply ucmra_unit_least.
      apply prod_included'. simpl. split; try done.
      apply prod_included'. simpl. split; try done.
      by apply ucmra_unit_least.
    }
    iSpecialize ("HH" with "[HIsSus Hℓ HCancHandle HThreadNoPerms HCell]").
    { iFrame. iExists _. iFrame "HArrMapsto Hℓ HRendThread HTh HCell". }
    iAssert (own γtq (◯ (ε, {[i := (ε, MaxNat 1, None)]})))
      with "[-]" as "#HInit".
    {
      iApply (own_mono with "HFrag").
      apply auth_included. simpl; split; try done.
      apply prod_included. simpl; split; try done.
      apply list_lookup_included. clear.
      induction i; case; simpl; try done.
      apply Some_included; right. apply prod_included.
      split; try done. simpl.
      apply prod_included'. simpl. split.
      apply ucmra_unit_least. rewrite max_nat_included /=. lia. }
    iFrame.

    iMod ("HClose" with "[-HCloseCell]") as "$".
    2: by iMod ("HCloseCell" with "[]"); [iLeft|done].

    iLeft.
    iFrame "HRendThread HTh".
    unfold cell_list_contents. iFrame.
    iSplitR; first by iPureIntro.
    iSplitR; first by iPureIntro.
    iSplitL "HFrag". {
      rewrite /inhabitant_token /rendezvous_state.
      iApply own_mono. 2: iApply "HFrag".
      apply auth_included. split; try done. simpl.
      apply prod_included'. split; try done. simpl.
      apply list_lookup_included. clear.
      induction i; case; simpl; try done.
      { apply Some_included. right. apply prod_included; split; try done; simpl.
        repeat (apply prod_included'; split); simpl; try done;
          apply ucmra_unit_least.
      }
    }
    rewrite HSameLength. rewrite insert_length HSameLength.
    subst. rewrite list_insert_alter. iFrame.
    iSplitR.
    2: by rewrite big_sepL_later.
    repeat rewrite big_sepL_forall.
    iIntros (k x).
    destruct (decide (i = (deqFront + k)%nat)).
    {
      subst i. rewrite lookup_drop list_lookup_alter.
      destruct (l !! (deqFront + k)%nat); simpl.
      2: done.
      iIntros (HH). simplify_eq. eauto.
    }
    iSpecialize ("HNotDone" $! k x). repeat rewrite lookup_drop.
    rewrite list_lookup_alter_ne. 2: lia.
    iIntros (HH). iApply "HNotDone". by iPureIntro.
  }
Qed.

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

Theorem resume_rendezvous_spec E R γa γtq γe γd i ℓ:
  is_infinite_array _ _ array_spec NArr γa (rendezvous_initialized γtq) -∗
  deq_front_at_least γtq (S i) -∗
  cell_location γtq γa i ℓ -∗
  iterator_issued γd i -∗
  <<< ∀ l deqFront, ▷ cell_list_contents E R γa γtq γe γd l deqFront >>>
    getAndSet #ℓ RESUMEDV @ ⊤ ∖ ↑N
  <<< ∃ v, ⌜l !! i = Some None⌝ ∧ ⌜v = NONEV⌝ ∧
             rendezvous_filled γtq i ∗
           ▷ E ∗
           ▷ cell_list_contents E R γa γtq γe γd
             (<[i := Some cellFilled]> l) deqFront ∨

           (∃ γt th, ⌜l !! i = Some (Some (cellInhabited γt th None))⌝ ∧
           ⌜v = InjLV #th⌝ ∧
           rendezvous_resumed γtq i ∗
           ▷ E ∗
           ▷ cell_list_contents E R γa γtq γe γd
           (<[i := Some (cellInhabited γt th (Some cellResumed))]> l) deqFront ∗
           resumer_token γtq i ∨

           ⌜l !! i = Some (Some (cellInhabited γt th (Some (cellCancelled None))))⌝ ∧
           ⌜v = InjLV #th⌝ ∧
           rendezvous_cancelled γtq i ∗
           ▷ rendezvous_thread_handle γtq γt th i ∗
           thread_doesnt_have_permits γt ∗
           ▷ E ∗ ▷ resumer_token γtq i ∗
           ▷ cell_list_contents E R γa γtq γe γd
           (<[i := Some (cellInhabited γt th (Some (cellCancelled (Some cancellationPrevented))))]> l) deqFront ∨

           ⌜l !! i = Some (Some (cellInhabited γt th (Some (cellCancelled (Some cancellationFinished)))))⌝ ∧
           (⌜v = CANCELLEDV⌝ ∧
            awakening_permit γtq) ∗
           ▷ cell_list_contents E R γa γtq γe γd l deqFront ∨

           ⌜l !! i = Some (Some (cellInhabited γt th (Some cellAbandoned)))⌝ ∧
           ⌜v = InjLV #th⌝ ∧
           rendezvous_abandoned γtq i ∗
           ▷ E ∗
           thread_doesnt_have_permits γt ∗
           ▷ cell_list_contents E R γa γtq γe γd l deqFront),
        RET v >>>.
Proof.
  iIntros "#HCellInv #HDeqFrontLb #HArrMapsto HIsRes" (Φ) "AU".

  awp_apply getAndSet_spec. rewrite /atomic_acc.
  iMod (acquire_cell _ _ _ _ _ ⊤ with "HArrMapsto")
    as "[HCell HCloseCell]"; first done.
  iMod "AU" as (l deqFront) "[(>% & #HNotDone & >HAuth & HCellResources) HCloseAU]".

  iDestruct (deq_front_at_least__cell_list_contents
             with "HDeqFrontLb HAuth") as %HDeqFront.
  repeat rewrite big_sepL_later.
  iMod (own_update with "HAuth") as "[HAuth HExistsEl']".
  2: iDestruct (exists_list_element_lookup _ _ i with "HExistsEl' HAuth")
    as %[cr HIsSome].
  {
    apply auth_update_core_id. apply _.
    apply prod_included; split; simpl.
    apply ucmra_unit_least.
    apply list_lookup_included.
    intros j. rewrite map_lookup.
    destruct (decide (i = j)).
    {
      subst.
      rewrite list_lookup_singletonM.
      assert (is_Some (l !! j)) as [? ->].
      by apply lookup_lt_is_Some; lia.
      simpl.
      apply Some_included_total.
      apply ucmra_unit_least.
    }
    assert (forall (A: ucmraT) (i i': nat) (x: A),
                (i' < i)%nat -> list_singletonM i x !! i' = Some (ε: A))
            as HH.
    {
      clear. induction i; intros [|i']; naive_solver auto with lia.
    }
    assert (forall (A: ucmraT) (i i': nat) (x: A),
                (i < i')%nat -> list_singletonM i x !! i' = None)
            as HH'.
    {
      clear. induction i; intros [|i']; naive_solver auto with lia.
    }
    destruct (decide (i < j)%nat).
    {
      rewrite HH'.
      by apply option_included; auto.
      lia.
    }
    rewrite HH.
    2: lia.
    assert (is_Some (l !! j)) as [? ->].
    by apply lookup_lt_is_Some; lia.
    simpl.
    apply Some_included_total.
    apply ucmra_unit_least.
  }

  destruct cr; simpl in *.
  2: {
    iDestruct "HCell" as "[>#HCellInit|[Hℓ HCancHandle]]".
    {
      iExFalso.
      rewrite /rendezvous_initialized /rendezvous_state.
      iDestruct (own_valid_2 with "HAuth HCellInit") as
          %[[_ HValid]%prod_included _]%auth_both_valid.
      iPureIntro.
      move: HValid. simpl. rewrite list_lookup_included.
      intros HValid. specialize (HValid i). rewrite map_lookup in HValid.
      rewrite HIsSome in HValid. simpl in *.
      move: HValid. clear. induction i.
      - simpl. rewrite Some_included_total.
        intros HH.
        apply prod_included in HH; simpl in HH.
        destruct HH as [HH _].
        apply prod_included in HH; simpl in HH.
        destruct HH as [_ HH].
        apply max_nat_included in HH. simpl in *.
        lia.
      - done.
    }
    iAssert (▷ ℓ ↦ InjLV #() ∧ ⌜val_is_unboxed (InjLV #())⌝)%I with "[Hℓ]" as "HAacc".
    by iFrame.
    iExists _. iFrame "HAacc". iModIntro. iSplit.
    {
      iIntros "[Hℓ _]". iDestruct "HCloseAU" as "[HCloseAU _]".
      iSpecialize ("HCloseCell" with "[Hℓ HCancHandle]").
      by iRight; iFrame.
      iFrame "HIsRes". iMod ("HCloseAU" with "[-HCloseCell]") as "$".
      2: done.
      repeat rewrite -big_sepL_later.
      iFrame "HNotDone". iFrame. by iPureIntro; lia.
    }
    iIntros "Hℓ".

    remember (<[i := Some cellFilled]> l) as l'.

    iMod (own_update _ _ (● cell_list_contents_auth_ra l' deqFront ⋅
                            (◯ (ε, {[i := (ε, cellDoneO, Some (to_agree cellFilled))]}) ⋅
                             ◯ (ε, {[i := (ε, cellDoneO, ε)]}))
                         )
            with "HAuth") as "[HAuth [HFrag1 HFrag2]]".
    {
      rewrite -auth_frag_op -pair_op list_singletonM_op ucmra_unit_left_id.
      rewrite -pair_op ucmra_unit_right_id -core_id_dup.
      apply auth_update_alloc. unfold cell_list_contents_auth_ra.
      replace (length l') with (length l).
      2: by subst; rewrite insert_length.
      apply prod_local_update_2; simpl.
      repeat rewrite -fmap_is_map.
      subst. rewrite list_fmap_insert /=.
      apply list_lookup_local_update. intros i'.
      rewrite /ε /list_unit lookup_nil.
      destruct (nat_eq_dec i i').
      {
        subst. rewrite !list_lookup_insert.
        2: rewrite fmap_length; lia.
        repeat rewrite map_lookup.
        rewrite list_lookup_singletonM.
        rewrite HIsSome. simpl.
        apply option_local_update'.
        apply prod_local_update; simpl; last by apply alloc_option_local_update.
        apply prod_local_update_2.
        apply max_nat_local_update. simpl. lia.
      }
      rewrite list_lookup_insert_ne; last done.
      rewrite map_lookup.

      destruct (decide (i' < i)) as [HLt|HGe].
      {
        assert (is_Some (l !! i')) as [x ->] by (apply lookup_lt_is_Some; lia).
        simpl.
        assert (forall (A: ucmraT) (i i': nat) (x: A),
                   (i' < i)%nat -> list_singletonM i x !! i' = Some (ε: A))
               as HH.
        {
          clear. induction i; intros [|i']; naive_solver auto with lia.
        }
        rewrite HH. 2: lia.
        by apply option_local_update'.
      }

      remember (l !! i') as Z.

      rewrite lookup_ge_None_2 //.
      rewrite list_singletonM_length. lia.
    }
    iSpecialize ("HCloseCell" with "[HFrag2]").
    {
      iLeft.
      iApply (own_mono with "HFrag2").
      apply auth_included; simpl. split; first done.
      apply prod_included; simpl. split; first done.
      apply list_singletonM_included. eexists.
      rewrite list_lookup_singletonM. split; first done.
      apply prod_included'; simpl. split; last done.
      apply prod_included'; simpl. split; first done.
      apply max_nat_included. simpl. lia.
    }
    iDestruct "HCloseAU" as "[_ HCloseAU]".
    iMod ("HCloseAU" with "[-HCloseCell]") as "$"; last done.
    iLeft.
    repeat (iSplitR; first done).
    rewrite /rendezvous_filled /rendezvous_done /rendezvous_state.
    iFrame "HFrag1 HAuth".
    iAssert (⌜deqFront <= length l'⌝)%I as "$".
    {
      iPureIntro. subst. rewrite insert_length. done.
    }
    subst.
    replace (<[i := Some cellFilled]> l)
            with (<[(length (take i l) + O)%nat := Some cellFilled]> l).
    2: { rewrite take_length_le. 2: lia. by rewrite -plus_n_O. }
    remember (take i l) as lln.
    replace l with (take i l ++ None :: drop (S i) l).
    2: by apply take_drop_middle.
    subst.
    rewrite insert_app_r. simpl.
    destruct (deqFront - i)%nat eqn:Z. lia.
    rewrite !big_sepL_app /=.
    rewrite -!big_sepL_later.
    iDestruct "HCellResources" as "(HRRsH & [$ HR] & HRRsT)".
    rewrite -plus_n_O.
    iFrame.
    repeat rewrite drop_app_ge take_length_le; try lia.
    rewrite Z. simpl. iFrame "HNotDone".
    iExists ℓ. iFrame.
    iFrame "HArrMapsto".
    iRight. iFrame. rewrite decide_True; last lia.
    by iFrame.
  }

  destruct c as [|γt th o].
  { (* Cell is filled. *)
    iDestruct (big_sepL_lookup_acc with "[HCellResources]")
      as "[HR HCellRRsRestore]"; simpl; try done.
    simpl.
    iDestruct "HR" as (?) "(_ & >HIsRes' & _)".
    iDestruct (iterator_issued_exclusive with "HIsRes HIsRes'") as %[].
  }
  destruct o as [d|].
  2: {
    iDestruct (big_sepL_insert_acc _ _ i with "[HCellResources]")
      as "[HR HCellRRsRestore]"; simpl; try done.
    simpl.
    iDestruct "HR" as (ℓ') "(HArrMapsto' & HThread & HIsSus & HCancHandle)".
    iDestruct (infinite_array_mapsto_agree with "HArrMapsto HArrMapsto'") as "><-".
    iDestruct "HThread" as "(Hℓ & >HNotPerms & #HRend)".
    iAssert (▷ ℓ ↦ InjLV #th ∧ ⌜val_is_unboxed (InjLV #th)⌝)%I
      with "[Hℓ]" as "HAacc".
    by iFrame.

    iSpecialize ("HCloseCell" with "HCell").

    iExists _. iFrame "HAacc". iModIntro. iSplit.
    {
      iIntros "[Hℓ _]". iFrame "HIsRes".
      iDestruct "HCloseAU" as "[HCloseAU _]".
      iMod ("HCloseAU" with "[-HCloseCell]") as "$"; last done.
      iSpecialize ("HCellRRsRestore" $! _). rewrite list_insert_id //.
      repeat rewrite -big_sepL_later.
      iFrame "HNotDone". iFrame.
      iSplitR; first done.
      iApply "HCellRRsRestore".
      iExists ℓ. iFrame. eauto.
    }
    iSpecialize ("HCellRRsRestore"
                   $! (Some (cellInhabited γt th (Some cellResumed)))).

    iIntros "Hℓ".
    iMod (own_update with "HAuth") as "[HAuth [HFrag HRes]]".
    2: {
      iMod ("HCloseAU" with "[-HCloseCell]") as "$"; last done.
      iRight.
      iExists γt, th. iLeft.
      iSplitR; first done. iSplitR; first done.
      iSplitL "HFrag". by iExists γt, th; iFrame.
      rewrite /cell_list_contents insert_length.
      iAssert (⌜deqFront <= length l⌝)%I as "$"; first done.
      iFrame "HAuth HRes".
      rewrite drop_insert_gt; last lia.
      rewrite -!big_sepL_later.
      iFrame "HNotDone".
      rewrite take_insert_lt; last lia.
      erewrite <-(take_drop_middle l); last done.
      rewrite take_app_ge take_length_le; try lia.
      rewrite !insert_app_r_alt take_length_le; try lia.
      rewrite !Nat.sub_diag /=.
      rewrite !count_matching_app /= !replicate_plus !big_sepL_app /=.
      iDestruct "HEs" as "($ & $ & $)".
      destruct (deqFront - i) eqn:Z; first lia. simpl.
      iDestruct "HRs" as "($ & HR & $)".
      iDestruct ("HCellRRsRestore" with "[HIsRes HArrMapsto HIsSus HCancHandle Hℓ HR HNotPerms]")
        as "$".
      { iExists _. iFrame "HArrMapsto HIsRes HCancHandle HIsSus HRend". iRight. iFrame. }
    }
    rewrite -auth_frag_op -pair_op ucmra_unit_right_id list_singletonM_op.

    apply auth_update_alloc, prod_local_update'; simpl.
    by rewrite insert_length /=.

    repeat rewrite -fmap_is_map. repeat rewrite fmap_app. simpl.
    assert (i < length l)%nat as HLt by lia.

    apply list_lookup_local_update. intros i'.
    rewrite list_fmap_insert lookup_nil.
    destruct (lt_eq_lt_dec i' i) as [[HLti'| ->]|HGei'].
    - rewrite list_lookup_singletonM_lt; last lia.
      rewrite list_lookup_insert_ne; last lia.
      rewrite list_lookup_fmap.
      assert (is_Some (l !! i')) as [? ->]=> /=.
      by apply lookup_lt_is_Some; lia.
      by apply option_local_update'.
    - rewrite list_insert_alter list_lookup_alter.
      rewrite list_lookup_fmap list_lookup_singletonM HIsSome /=.
      apply option_local_update'.
      repeat apply prod_local_update'=> /=.
      * done.
      * done.
      * by apply alloc_option_local_update.
      * apply max_nat_local_update=> /=. lia.
      * by apply alloc_option_local_update.
    - rewrite list_lookup_insert_ne; last lia.
      rewrite list_lookup_singletonM_gt; last lia.
      done.
  }

  repeat rewrite -big_sepL_later.
  destruct d; simpl.
  2: { (* Resumed? Impossible. *)
    iDestruct (big_sepL_lookup_acc with "HCellResources")
      as "[HR HCellRRsRestore]"; simpl; first done.
    iDestruct "HR" as (?) "(_ & _ & _ & >HIsRes' & _)".
    iDestruct (iterator_issued_exclusive with "HIsRes HIsRes'") as %[].
  }

  { (* Cancelled. *)
    iDestruct (big_sepL_insert_acc with "HCellResources")
      as "[HR HCellRRsRestore]"; simpl; first done.
    iSpecialize ("HCloseCell" with "HCell").
    iDestruct "HR" as (ℓ') "(HArrMapsto' & #HRend & HIsSus & HInhToken' & HH)".
    iDestruct (infinite_array_mapsto_agree with "HArrMapsto HArrMapsto'") as "><-".
    rewrite !decide_True; last lia.
    destruct resolution as [[|]|].
    2: iDestruct "HH" as "[HIsRes' _]".
    1: iDestruct "HH" as "[HCancToken [[_ HIsRes']|[[Hℓ >HAwak]|(_ & HIsRes' & _)]]]".
    all: try by iDestruct (iterator_issued_exclusive with "HIsRes HIsRes'") as ">[]".
    1: remember CANCELLEDV as v.
    2: iDestruct "HH" as "(Hℓ & HE & HCancHandle & >HNoPerms & >HAwak)";
      remember (InjLV #th) as v.
    all: iAssert (▷ ℓ ↦ v ∧ ⌜val_is_unboxed v⌝)%I with "[Hℓ]" as "HAacc";
      first by (iFrame; iPureIntro; subst; done).
    {
      iExists _. iFrame "HAacc". iModIntro. iSplit.
      {
        iIntros "[Hℓ _]". iFrame "HIsRes". iDestruct "HCloseAU" as "[HCloseAU _]".
        iMod ("HCloseAU" with "[-HCloseCell]") as "$"; last done.
        iFrame "HEs HRs HAuth HNotDone". iSplitR; first done.
        iSpecialize ("HCellRRsRestore" $! _); rewrite list_insert_id //.
        iApply "HCellRRsRestore".
        iExists _. iFrame "HArrMapsto HIsSus HInhToken' HRend".
        iFrame "HCancToken". iRight. iLeft.
        rewrite decide_True; last lia. subst; by iFrame.
      }
      {
        iIntros "Hℓ". iMod ("HCloseAU" with "[-HCloseCell]") as "$"; last done.
        iRight. iExists γt, th. iRight. iRight. iLeft.

        iSplitR; first done. iFrame "HAwak". iSplitR; first done.
        iSplitR; first by iPureIntro; lia.
        iSpecialize ("HCellRRsRestore" $! _); rewrite list_insert_id //.
        iFrame "HAuth HEs HRs HNotDone". iApply "HCellRRsRestore".
        iExists _. iFrame "HArrMapsto HRend HIsSus HInhToken'".
        iFrame "HCancToken". iLeft. iFrame.
      }
    }
    {
      iExists _. iFrame "HAacc". iModIntro. iSplit.
      {
        iIntros "[Hℓ _]". iFrame "HIsRes".
        iDestruct "HCloseAU" as "[HCloseAU _]".
        iMod ("HCloseAU" with "[-HCloseCell]") as "$"; last done.
        iFrame "HNotDone HEs HRs HAuth". iSplitR; first done.
        iSpecialize ("HCellRRsRestore" $! _); rewrite list_insert_id //.
        iApply "HCellRRsRestore".
        iExists _. iFrame "HArrMapsto HIsSus HInhToken' HRend". subst.
        rewrite decide_True; last lia. iFrame.
      }
      {
        iIntros "Hℓ".
        iMod (own_update with "HAuth") as "[HAuth [HFrag1 [HFrag2 HFrag3]]]".
        2: {
          iMod ("HCloseAU" with "[-HCloseCell]") as "$"; last done.
          iRight. iExists γt, th. iRight. iLeft.

          iSplitR; first done. iSplitR; first done.
          rewrite /rendezvous_cancelled.
          iAssert (rendezvous_state γtq i (ε, {| max_nat_car := 5 |},
            Some (to_agree (cellInhabited γt th (Some (cellCancelled
              (Some cancellationPrevented))))))) with "HFrag3" as "_".
          iFrame "HRend HNoPerms HE HFrag1 HFrag2".
          iFrame "HAuth".
          rewrite insert_length. iSplitR; first done.
          rewrite drop_insert_gt; last lia. iFrame "HNotDone".
          rewrite take_insert_lt; last lia.
          iSplitL "HEs". 2: iSplitL "HRs".
          {
            rewrite list_insert_alter. erewrite count_matching_alter=> //.
            simpl. by rewrite Nat.sub_0_r Nat.add_0_r.
          }
          {
            rewrite list_insert_alter. erewrite count_matching_alter=> //.
            2: by rewrite lookup_take; last lia.
            simpl. by rewrite Nat.sub_0_r Nat.add_0_r.
          }
          {
            iSpecialize ("HCellRRsRestore" $! _). rewrite bi.later_wand.
            iApply "HCellRRsRestore". simpl. iExists _.
            iFrame "HArrMapsto HRend HIsSus HInhToken' HIsRes HCancHandle".
            iLeft. by iFrame.
          }
        }
        {
          rewrite /cell_list_contents_auth_ra /= insert_length.
          apply auth_update_alloc, prod_local_update_2=> /=.
          rewrite !list_singletonM_op.
          erewrite list_fmap_insert.
          apply list_lookup_local_update. intros j.
          rewrite lookup_nil map_lookup.
          destruct (lt_eq_lt_dec j i) as [[HLt| ->]|HGt].
          - rewrite list_lookup_insert_ne; last lia.
            rewrite list_lookup_singletonM_lt; last lia.
            rewrite list_lookup_fmap.
            assert (is_Some (l !! j)) as [? ->].
            by apply lookup_lt_is_Some; lia.
            simpl.
            by apply option_local_update'.
          - rewrite list_lookup_insert; last rewrite fmap_length; last lia.
            rewrite list_lookup_singletonM HIsSome /=.
            apply option_local_update'.
            repeat (apply prod_local_update=> //=).
            * by apply alloc_option_local_update.
            * rewrite max_nat_op_max /=.
              apply max_nat_local_update=> /=. lia.
            * by apply alloc_option_local_update.
          - rewrite list_lookup_insert_ne; last lia.
            rewrite list_lookup_singletonM_gt; last lia.
            rewrite map_lookup. done.
        }
      }
    }
  }
  (* Abandoned *)
  iDestruct (big_sepL_lookup_acc with "HCellResources")
    as "[HR HCellRRsRestore]"; simpl; first done.

  iMod (rendezvous_done_from_auth with "HAuth") as "[HAuth HIsAbandoned]"; first done.
  right; eauto.
  iAssert (rendezvous_done γtq i (cellInhabited γt th (Some cellAbandoned)))
             with "HIsAbandoned" as "HIsAbandoned".

  iDestruct "HR" as (?) "(HArrMapsto' & #HRend & HCancHandle & HIsSus & HInh & HDeqFront & HH)".
  iDestruct "HH" as "[>HIsRes'|(HE & Hℓ & >HNoPerms)]".
  by iDestruct (iterator_issued_exclusive with "HIsRes HIsRes'") as %[].
  iDestruct (infinite_array_mapsto_agree with "HArrMapsto HArrMapsto'") as "><-".

  iAssert (▷ ℓ ↦ InjLV #th ∧ ⌜val_is_unboxed (InjLV #th)⌝)%I
    with "[Hℓ]" as "HAacc".
  by iFrame.

  iSpecialize ("HCloseCell" with "HCell").
  iExists _. iFrame "HAacc". iModIntro. iSplit.

  {
    iIntros "[Hℓ _]". iFrame "HIsRes".
    iDestruct "HCloseAU" as "[HCloseAU _]".
    iMod ("HCloseAU" with "[-HCloseCell]") as "$"; last done.
    iFrame. iSplitR; first done. iFrame "HNotDone".
    iApply "HCellRRsRestore". iExists _; iFrame "HArrMapsto"; iFrame.
    iFrame "HRend".
    iRight. iFrame.
  }

  iIntros "Hℓ".
  iMod ("HCloseAU" with "[-HCloseCell]") as "$"; last done.
  iRight. iExists γt, th.
  repeat iRight.

  iSplitR; first done.
  iSplitR; first by eauto.
  iFrame.
  iSplitL "HIsAbandoned".
  by iExists _, _.
  iSplitR; first done. iFrame "HNotDone".
  iApply "HCellRRsRestore".
  iExists _; iFrame "HArrMapsto". by iFrame.
Qed.

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

Lemma iterator_counter_is_at_least γ ℓ n:
  iterator_counter γ ℓ n ==∗ iterator_counter γ ℓ n ∗ iterator_counter_at_least γ n.
Proof.
  iIntros "($ & HAuth)". rewrite /iterator_counter_at_least.
  iMod (own_update with "HAuth") as "[$ $]".
  2: done.
  apply auth_update_core_id.
  by apply _.
  rewrite prod_included; simpl.
  split.
  by apply ucmra_unit_least.
  apply max_nat_included; simpl; lia.
Qed.

Lemma cancelled_cell_is_cancelled_rendezvous' S R γa γtq γe γd i l deqFront:
  cell_is_cancelled _ _ _ NArr γa i -∗
  rendezvous_initialized γtq i -∗ cell_list_contents S R γa γtq γe γd l deqFront -∗
  ∃ γt th r, ⌜l !! i = Some (Some (cellInhabited γt th (Some (cellCancelled r))))⌝.
Proof.
  iIntros "HCanc HInit HListContents".
  rewrite /cell_list_contents /rendezvous_initialized.
  iDestruct "HListContents" as "(_ & _ & HOwn & _ & _ & HRRs)".
  iDestruct (own_valid_2 with "HOwn HInit")
    as %[[_ HValid]%prod_included _]%auth_both_valid.
  simpl in *.
  move: HValid. rewrite list_lookup_included. move=> HValid.
  specialize (HValid i).
  rewrite list_lookup_singletonM in HValid.
  rewrite map_lookup in HValid.
  destruct (l !! i) as [s|] eqn:Z.
  2: {
    move: HValid. rewrite option_included. case; first done.
    intros (? & ? & _ & HContra & _).
    discriminate.
  }
  destruct s as [s'|].
  2: {
    simpl in *. move: HValid. rewrite Some_included_total.
    intros HH.
    apply prod_included in HH; destruct HH as [HH _].
    apply prod_included in HH; destruct HH as [_ HH].
    move: HH. simpl.
    rewrite max_nat_included /=. lia.
  }
  iDestruct (big_sepL_lookup with "HRRs") as "HR"; first done.
  simpl.
  iDestruct "HR" as (?) "[_ HR]".
  destruct s' as [|? ? [o|]]; simpl in *.
  2: destruct o; eauto.
  1: iDestruct "HR" as "(_ & HCancHandle & _)".
  2: iDestruct "HR" as "(_ & _ & _ & HCancHandle & _)".
  3: iDestruct "HR" as "(_ & _ & HCancHandle & _)".
  4: iDestruct "HR" as "(_ & _ & HCancHandle)".
  all: by iDestruct (cell_cancellation_handle_not_cancelled with "HCanc HCancHandle")
      as %[].
Qed.

Lemma awakening_permit_from_cancelled_cell' E R γa γtq γe γd i γt th deqFront r:
  ⌜i < deqFront⌝ -∗
  cell_is_cancelled _ _ _ NArr γa i -∗
  iterator_issued γd i -∗
  cell_resources E R γtq γa γe γd deqFront i (Some (cellInhabited γt th (Some (cellCancelled r)))) -∗
  cell_resources E R γtq γa γe γd deqFront i (Some (cellInhabited γt th (Some (cellCancelled r)))) ∗
  awakening_permit γtq.
Proof.
  simpl. iIntros (Hi) "HCellCanc HIsRes HR".
  iDestruct "HR" as (?) "(HArrMapsto & $ & $ & $ & HH)".
  rewrite decide_True; last lia.
  destruct (r) as [[|]|].
  - iDestruct "HH" as "[HCancToken [[_ HIsRes']|[[Hℓ $]|(_ & HIsRes' & _)]]]";
      try by iDestruct (iterator_issued_exclusive with "HIsRes HIsRes'") as %[].
    iExists _. iFrame "HArrMapsto HCancToken". iRight. iRight.
    iFrame.
  - iDestruct "HH" as "[HIsRes' _]".
    by iDestruct (iterator_issued_exclusive with "HIsRes HIsRes'") as %[].
  - iDestruct "HH" as "(_ & _ & HCancHandle & _)".
    by iDestruct (cell_cancellation_handle_not_cancelled with "HCellCanc HCancHandle") as %[].
Qed.

Lemma awakening_permit_from_cancelled_cell E R γa γtq γe γd deqFront l γt th r i:
  l !! i = Some (Some (cellInhabited γt th (Some (cellCancelled r)))) ->
  ⌜i < deqFront⌝ -∗
  cell_is_cancelled _ _ _ NArr γa i -∗
  iterator_issued γd i -∗
  cell_list_contents E R γa γtq γe γd l deqFront -∗
  awakening_permit γtq ∗ cell_list_contents E R γa γtq γe γd l deqFront.
Proof.
  iIntros (HEl Hi) "HCanc HIsRes HListContents".
  iDestruct (cell_list_contents_lookup_acc with "HListContents")
    as "[HR HListContents]"; first done.
  iDestruct (awakening_permit_from_cancelled_cell' with "[% //] HCanc HIsRes HR")
            as "[HR $]".
  by iApply "HListContents".
Qed.

Theorem increase_deqIdx E R γa γtq γe γd (eℓ epℓ dℓ dpℓ: loc):
  ▷ awakening_permit γtq -∗
  <<< ∀ l deqFront, ▷ is_thread_queue E R γa γtq γe γd eℓ epℓ dℓ dpℓ l deqFront >>>
  ((iterator_step_skipping_cancelled segment_size) #dpℓ) #dℓ @ ⊤
  <<< ∃ (ix: nat) (ℓ: loc),
          ▷ is_thread_queue E R γa γtq γe γd eℓ epℓ dℓ dpℓ l deqFront ∗
            iterator_issued γd ix ∗
            segment_location γa (ix `div` Pos.to_nat segment_size)%nat ℓ,
     RET (#ℓ, #(ix `rem` Pos.to_nat segment_size))%V >>>.
Proof.
  iIntros "HAwaken" (Φ) "AU". iLöb as "IH".

  wp_lam. wp_pures. wp_bind (!_)%E.

  iMod "AU" as (? ?) "[(HInfArr & HListContents & >% & HRest) [HClose _]]".
  iDestruct "HRest" as (? deqIdx) "(HEnqIt & >HDeqIt & HRest)".
  iMod (read_iterator with "HDeqIt") as
      (hId hℓ Hhl) "(Hpℓ & #HSegLoc & #HCounter & HRestore)".
  wp_load.
  iMod ("HClose" with "[HInfArr HListContents HEnqIt HRest Hpℓ HRestore]") as "AU".
  { iFrame "HInfArr HListContents".
    iDestruct ("HRestore" with "Hpℓ") as "HIterator".
    iSplitR; first by iPureIntro.
    iExists _, deqIdx. by iFrame.
  }

  iModIntro. wp_pures.
  wp_bind (FAA _ _).
  awp_apply iterator_value_faa. iApply (aacc_aupd_abort with "AU"); first done.
  iIntros (? deqFront) "(HInfArr & HListContents & >% & HRest)".
  iDestruct "HRest" as (? deqIdx') "(HEnqIt & >HDeqIt & >HRest)".
  iDestruct (iterator_points_to_at_least with "HCounter [HDeqIt]") as %HLet.
  by iDestruct "HDeqIt" as "[$ _]".
  (* Here I must prove that deqIdx' + 1 <= deqFront *)
  iDestruct "HRest" as "(HRest & HRest'' & HRest')".

  iDestruct (awakening_permit_implies_bound 1
               with "[HRest'] [HAwaken] [HDeqIt] HRest HListContents")
    as "#>%".
  by iDestruct "HRest'" as "%"; iPureIntro; lia.
  by iFrame.
  by iDestruct "HDeqIt" as "[$ _]".

  iAaccIntro with "HDeqIt".
  { iIntros "HIsIter". iFrame "HInfArr HListContents".
    iSplitL "HEnqIt HRest HRest' HRest'' HIsIter".
    iSplitR; first done.
    by eauto with iFrame.
    by iIntros "!> $". }
  iIntros "[HIsIter HPerms]".
  iDestruct "HIsIter" as "[HDeqCtr HDeqLoc]".
  iMod (iterator_counter_is_at_least with "HDeqCtr")
    as "[HDeqCtr HCounter']".
  iClear "HCounter".
  iDestruct "HCounter'" as "#HCounter".
  rewrite /= union_empty_r_L.
  replace (own γd _) with (iterator_issued γd deqIdx') by
      rewrite Nat.add_1_r //.

  iFrame "HInfArr HListContents".
  iSplitR "HPerms".
  { iSplitR; first done.
    iExists _, _. iFrame.
    rewrite seq_add big_sepL_app.
    iDestruct "HRest'" as "[% %]".
    simpl.
    iFrame.
    iPureIntro.
    repeat split; try done.
  }
  iIntros "!> AU !>".

  wp_pures. wp_bind (find_segment _ _ _).
  remember (Z.quot _ _) as K.
  replace K with (Z.of_nat (deqIdx' `div` Pos.to_nat segment_size)%nat).
  2: subst; by rewrite quot_of_nat.
  awp_apply find_segment_spec; try done; first by iApply tq_cell_init.
  iApply (aacc_aupd_abort with "AU"); first done.
  clear K HeqK.
  iIntros (? ?) "(HInfArr & HRest)".
  iAaccIntro with "HInfArr"; iFrame "HRest".
  by iIntros "$ !> $ !>".
  iIntros (tId ?) "($ & #(HSegInv & HSegLoc' & HH)) !> AU !>".

  wp_pures. awp_apply segment_id_spec. iApply (aacc_aupd with "AU"); first done.
  iIntros (? ?) "(HInfArr & HRest)".
  iDestruct (is_segment_by_location with "HSegLoc' HInfArr")
    as (? ?) "[HIsSeg HInfArrRestore]".
  iAaccIntro with "HIsSeg"; iFrame "HRest".
  {
    iIntros "HIsSeg". iDestruct ("HInfArrRestore" with "HIsSeg") as "$".
    by iIntros "!> $ !>".
  }
  iIntros "HIsSeg". iDestruct (bi.later_wand with "HInfArrRestore HIsSeg") as "$".

  iDestruct "HH" as "[(% & <-)|(% & % & HCanc)]".
  {
    (* deqIdx' <= the head id * segment_size *)
    assert (hId = deqIdx' `div` Pos.to_nat segment_size)%nat as ->.
    { eapply find_segment_id_bound; try lia. done. lia. }
    (* This means that the head is the segment that we needed all along. *)
    iRight.
    iExists _, _. iFrame "HPerms HSegLoc'".
    iIntros "!> HΦ !>". wp_pures. rewrite bool_decide_eq_true_2 //.
    wp_pures.
    (* I need to provide proper return predicates. *)

    done.
  }

  (* the head id * segment_size < deqIdx' *)
  destruct (decide (tId = (deqIdx' `div` Pos.to_nat segment_size)%nat)).
  {
    (* But is the segment id still what we were looking for? *)
    iRight.
    iExists _, _. subst. iFrame "HPerms HSegLoc'".
    iIntros "!> HΦ !>". wp_pures. rewrite bool_decide_eq_true_2.
    2: by subst.
    wp_pures.
    done.
  }

  iLeft. iIntros "!> AU !>". wp_pures. rewrite bool_decide_eq_false_2.
  2: {
    intros HContra. inversion HContra as [HContra'].
    apply Nat2Z.inj in HContra'. subst. lia.
  }
  wp_pures.

  awp_apply segment_id_spec. iApply (aacc_aupd_abort with "AU"); first done.
  iIntros (? ?) "(HInfArr & HRest)".
  iDestruct (is_segment_by_location with "HSegLoc' HInfArr")
    as (? ?) "[HIsSeg HInfArrRestore]".
  iAaccIntro with "HIsSeg"; iFrame "HRest".
  {
    iIntros "HIsSeg". iDestruct ("HInfArrRestore" with "HIsSeg") as "$".
    by iIntros "!> $ !>".
  }
  iIntros "HIsSeg". iDestruct (bi.later_wand with "HInfArrRestore HIsSeg") as "$".

  rewrite segments_cancelled__cells_cancelled.
  (* I need to get my acquire permit back from the cancelled segment. *)
  (* First, I need to learn that my cell is truly cancelled. *)
  remember (deqIdx' `div` Pos.to_nat segment_size)%nat as deqSeg.
  iAssert ([∗ list] id ∈ seq deqIdx' (tId * Pos.to_nat segment_size - deqIdx'),
           (∃ ℓ, inv N (cell_invariant γtq γa id ℓ)) ∗ cell_is_cancelled segment_size γa id)%I
          as "#HEv".
  {
    repeat rewrite big_sepL_forall.
    iIntros (k ? HEv).
    apply seq_lookup' in HEv. destruct HEv as [-> HEv].
    iSplit.
    - iSpecialize ("HSegInv" $! ((deqIdx' + k) `div` Pos.to_nat segment_size)%nat _).
      iDestruct ("HSegInv" with "[]") as "HSegInv'".
      { iPureIntro. apply seq_lookup. apply Nat.div_lt_upper_bound; lia. }
      iDestruct (cell_invariant_by_segment_invariant with "HSegInv'") as "HH".
      by apply (Nat.mod_upper_bound (deqIdx' + k)); lia.
      iDestruct "HH" as (ℓ) "[#HCellInv _]". simpl.
      iClear "HCanc". rewrite Nat.mul_comm -Nat.div_mod. by eauto.
      lia.
    - iSpecialize ("HCanc" $! (deqIdx' + k - deqSeg * Pos.to_nat segment_size)%nat).
      assert (deqSeg * Pos.to_nat segment_size <= deqIdx' + k)%nat.
      {
        eapply transitivity.
        - rewrite Nat.mul_comm. subst.
          apply Nat.mul_div_le.
          lia.
        - lia.
      }
      iDestruct ("HCanc" with "[]") as "HCanc'".
      { iPureIntro. apply seq_lookup. rewrite Nat.mul_sub_distr_r. subst.
        apply Nat.lt_add_lt_sub_r.
        rewrite Nat.sub_add //. lia.
      }
      by rewrite Nat.add_sub_assoc // (Nat.add_comm _ (deqIdx' + k)) Nat.add_sub.
  }
  iClear "HSegInv HCanc".
  rewrite big_sepL_forall.

  iAssert (□ [∗ list] k ∈ seq deqIdx' (tId * Pos.to_nat segment_size - deqIdx')%nat,
           |={⊤}=> cell_is_cancelled segment_size γa k ∗ rendezvous_initialized γtq k)%I
  as "#HEv'".
  {
    iIntros "!>".
    remember (seq _ _) as l'.
    iClear "IH HSegLoc HCounter HSegLoc'". clear.
    iInduction l' as [|? l'] "IH"; simpl; first done.
    iDestruct ("HEv" $! O with "[]") as "[HInv HCanc]"; first by eauto.
    iDestruct "HInv" as (?) "#HInv".
    iSplitL.
    2: {
      iApply "IH".
      iIntros "!>" (k ? HEl).
      iApply ("HEv" $! (S k)).
      by simpl.
    }
    iInv N as ">HOpen" "HClose".
    iDestruct "HOpen" as "[[HCancHandle _]|#HH]".
    by iDestruct (cell_cancellation_handle'_not_cancelled
                    with "HCancHandle HCanc") as %[].
    iFrame "HCanc HH".
    by iMod ("HClose" with "[$]").
  }

  rewrite big_sepL_fupd.

  iIntros "!> AU".
  iDestruct "HEv'" as ">#HEv'".

  iIntros "!>". wp_pures. rewrite -Nat2Z.inj_mul.

  awp_apply increase_value_to_spec.
  iApply (aacc_aupd_abort with "AU"); first done.
  iIntros (l newDeqFront) "(HInfArr & HListContents & >% & HRest)".
  iDestruct "HRest" as (? deqIdx'') "(HEnqIt & >HDeqIt & HRest)".
  iDestruct (iterator_points_to_at_least with "HCounter [HDeqIt]") as "%".
  by iDestruct "HDeqIt" as "[$ _]".
  iDestruct "HDeqIt" as "[HDeqCounter HDeqLoc]".
  iAaccIntro with "HDeqCounter".
  {
    iFrame "HPerms".
    iIntros "HDeqCounter !>". iSplitL.
    * iFrame "HInfArr HListContents".
      iSplitR; first done.
      iExists _, _. iFrame "HEnqIt HRest". by iFrame.
    * by iIntros "$".
  }

  iIntros "[HPerms' HV]". iFrame "HInfArr".

  assert (deqIdx' < deqIdx'')%nat as HL by lia.
  apply nat_lt_sum in HL. destruct HL as (d & ->).

  (* *)

  iDestruct "HV" as "[[% HDeqCounter]|[% HDeqCounter]]".
  {
    rewrite big_sepL_forall.
    iDestruct ("HEv'" $! O with "[]") as "[#HCanc #HInit]".
    {
      iPureIntro. apply seq_lookup. subst.
      assert (deqIdx' `div` Pos.to_nat segment_size < tId)%nat as HH by lia.
      assert (deqIdx' < tId * Pos.to_nat segment_size)%nat.
      2: lia.
      move: HH. clear. intros HH.

      induction tId. by inversion HH.
      inversion HH.
      2: subst; simpl; lia.
      clear. simpl.
      remember (deqIdx' `div` _)%nat as S.
      replace deqIdx' with (Pos.to_nat segment_size * S +
                            deqIdx' `mod` Pos.to_nat segment_size)%nat.
      2: subst; rewrite -Nat.div_mod; lia.
      rewrite Nat.add_comm Nat.mul_comm.
      apply plus_lt_le_compat. 2: done.
      apply Nat.mod_upper_bound. lia.
    }
    rewrite -plus_n_O.
    iDestruct (cancelled_cell_is_cancelled_rendezvous' with
                   "HCanc HInit HListContents") as (? ? ?) "#>%".
    iDestruct "HRest" as "(HAwak & HSusp & >[% %])".
    repeat rewrite big_sepL_later.
    iDestruct (awakening_permit_from_cancelled_cell with "HCanc HPerms HListContents")
              as "[HAwaken $]"; first done.
    iSplitR "HAwaken".
    2: {
      iIntros "!> AU !>". wp_pures.
      by iApply ("IH" with "HAwaken AU").
    }
    repeat rewrite -big_sepL_later.
    iSplitR; first done.
    iExists _, _. iFrame.
    by iPureIntro.
  }

  iAssert ([∗ list] i ∈ seq (deqIdx' + S d)
                    (tId * Pos.to_nat segment_size - (deqIdx' + S d)),
           (iterator_issued γd i ∗ cell_is_cancelled segment_size γa i))%I
    with "[HPerms']" as "HIsss".
  {
    iClear "IH HSegLoc HCounter HSegLoc' HEv".
    iEval (rewrite big_sepL_sep).
    iSplitL.
    2: {
      repeat rewrite big_sepL_forall.
      iIntros (? ? HEl).
      iDestruct ("HEv'" with "[]") as "[$ _]".
      iPureIntro.
      apply seq_lookup' in HEl. destruct HEl as [-> HLt].
      rewrite seq_lookup -Nat.add_assoc. done.
      lia.
    }
    remember (tId * Pos.to_nat segment_size - (deqIdx' + S d))%nat as Y.
    change (deqIdx' + S d)%nat with ((O + O) + (deqIdx' + S d))%nat.
    change (tId * Pos.to_nat segment_size)%nat with
        (tId * Pos.to_nat segment_size)%nat.
    remember (O + O)%nat as start.
    assert (start + Y <= tId * Pos.to_nat segment_size - (deqIdx' + S d)) as HStartInv.
    by subst; lia. clear Heqstart HeqY.
    iInduction Y as [|ih] "IH" forall (start HStartInv); simpl.
    done.
    remember (tId * Pos.to_nat segment_size)%nat as X.
    assert (X = (max (S (start + (deqIdx' + S d))) X)%nat) as HEqX
        by (subst; lia).
    rewrite HEqX.
    rewrite -max_nat_op_max -gset_disj_union.
    2: by apply set_seq_S_start_disjoint.
    rewrite pair_op auth_frag_op own_op.
    iDestruct "HPerms'" as "[$ HRec]".
    change (S (start + (deqIdx' + S d)))%nat with
        ((1 + start) + (deqIdx' + S d))%nat.
    iApply ("IH" with "[] [HRec]").
    2: by rewrite max_nat_op_max /= -HEqX.
    iPureIntro.
    simpl in *. rewrite /op /max_nat_op.
    lia.
  }

  (* *)

  iAssert ([∗ list] k ∈ seq deqIdx' (tId * Pos.to_nat segment_size - deqIdx'),
           ▷ ∃ γt th r, ⌜l !! k = Some (Some (cellInhabited γt th (Some (cellCancelled r))))⌝)%I
    as "#HEv''".
  {
    repeat rewrite big_sepL_forall.
    iIntros (k ? HEv). apply seq_lookup' in HEv. destruct HEv as [? HEv'].
    simplify_eq.
    iDestruct ("HEv'" $! k with "[]") as "[HCellCanc HRInit]".
    { iPureIntro. apply seq_lookup. lia. }
    by iDestruct (cancelled_cell_is_cancelled_rendezvous' with
                    "HCellCanc HRInit HListContents") as ">%".
  }

  rewrite -big_sepL_later.
  iDestruct "HEv''" as ">HEv''".

  iDestruct "HRest" as "(HRest' & HRest'' & >%)".

  iDestruct (big_sepL_lookup _ _ O with "HEv''") as %(? & ? & [? HEl]).
  by apply seq_lookup; lia.
  rewrite -plus_n_O in HEl.

  iDestruct (awakening_permit_from_cancelled_cell with "[] HPerms HListContents")
            as "[HAwaken HListContents]"; first done.
  {
    iDestruct (big_sepL_lookup with "HEv'") as "[$ _]".
    rewrite seq_lookup.
    - congr Some. done.
    - lia.
  }

  iAssert (▷(([∗ list] i ∈ seq (deqIdx' + S d)
                     (tId * Pos.to_nat segment_size - (deqIdx' + S d)),
            awakening_permit γtq) ∗
           cell_list_contents E R γa γtq γe γd l newDeqFront))%I
  with "[HListContents HIsss]" as "[>HAwaks $]".
  {
    iClear "IH HEv HSegLoc HCounter HSegLoc'".
    iAssert (⌜tId * Pos.to_nat segment_size <= length l⌝)%I as "%".
    {
      iDestruct (big_sepL_lookup
                   _ _ (tId * Pos.to_nat segment_size - deqIdx' - 1)%nat
                   with "HEv''") as (? ?) "HH".
      by apply seq_lookup; lia.
      iDestruct "HH" as %[? HH].
      assert (tId * Pos.to_nat segment_size - 1 < length l)%nat.
      {
        replace (deqIdx' + (_ - _))%nat with
            (tId * Pos.to_nat segment_size - 1)%nat in HH by lia.
        apply lookup_lt_is_Some; eauto.
      }
      iPureIntro; lia.
    }
    iDestruct "HListContents" as "($ & $ & $ & $ & $ & HListContents)".
    replace l with (take (deqIdx' + S d)%nat l ++ drop (deqIdx' + S d)%nat l).
    2: by rewrite take_drop.
    rewrite big_sepL_app.
    iDestruct "HListContents" as "[$ HListContents]".
    replace (drop (deqIdx' + S d) l) with
        (take (tId * Pos.to_nat segment_size - (deqIdx' + S d))
              (drop (deqIdx' + S d) l)
       ++ drop (tId * Pos.to_nat segment_size - (deqIdx' + S d))
              (drop (deqIdx' + S d) l)
        ).
    2: by rewrite take_drop.
    rewrite big_sepL_app.
    iDestruct "HListContents" as "[HListContents $]".

    rewrite big_sepL_later.
    remember (tId * Pos.to_nat segment_size - (deqIdx' + S d))%nat as len.
    remember (deqIdx' + S d)%nat as start.
    assert (start + len <= length l) as HOk.
    by subst; lia.

    iAssert (∀ i, ⌜(i < len)%nat⌝ -∗ ⌜∃ γt th r, drop start l !! i =
            Some (Some (cellInhabited γt th (Some (cellCancelled r))))⌝)%I as "#HEv'''".
    {
      iIntros (i HI).
      iDestruct (big_sepL_lookup _ _ (start + i - deqIdx')%nat with "HEv''") as %HH.
      by apply seq_lookup; subst; lia.
      subst.
      move: HH.
      rewrite lookup_app_r take_length_le.
      all: try lia.
      rewrite lookup_app_l.
      2: rewrite take_length_le.
      3: rewrite drop_length.
      all: try lia.
      rewrite lookup_drop.
      rewrite lookup_take.
      2: lia.
      rewrite lookup_drop.
      intros HH.
      iPureIntro.
      destruct HH as (γt & th & r & HH).
      exists γt, th, r.
      rewrite <- HH.
      congr (fun x => l !! x).
      lia.
    }

    iClear "HEv''".

    move: HOk.
    move: N. clear. intros N.
    intros HOk.

    rewrite take_length_le. 2: lia.

    remember (drop start l) as l'.
    assert (len <= length l')%nat as HOk'.
    by subst; rewrite drop_length; lia.

    clear HOk Heql' l.

    iInduction len as [|len'] "IH" forall (l' HOk' start); simpl in *; first done.
    destruct l' as [|x l']; first by inversion HOk'. simpl in *.
    iDestruct "HListContents" as "[HR HListContents]".
    iDestruct "HIsss" as "[HItIss HIsss]".
    iDestruct ("IH" with "[] [] [HListContents] HIsss") as "[$ HHH']".
    3: {
      iApply (big_sepL_mono with "HListContents").
      iIntros (k y HTake) "HV".
      by rewrite -plus_n_Sm.
    }
    by iPureIntro; lia.
    {
      iIntros "!>" (i HLt).
      iDestruct ("HEv'''" $! (S i)) as %HLt'.
      simpl in *.
      iPureIntro. apply HLt'. lia.
    }
    iDestruct (big_sepL_mono with "HHH'") as "$".
    { intros. iIntros "HH". by rewrite -plus_n_Sm. }
    iClear "IH".
    iDestruct ("HEv'''" $! O with "[]") as %(? & ? & ? & HIsCanc).
    by iPureIntro; lia.
    simpl in *.
    simplify_eq.
    rewrite -plus_n_O.
    iDestruct "HItIss" as "[HIsRes HCanc]".
    iDestruct (awakening_permit_from_cancelled_cell' with "HCanc HIsRes HR")
              as "[$ $]".
  }

  iSplitR "HAwaken".
  2: {
    iIntros "!> AU !>". wp_pures.
    iApply ("IH" with "HAwaken AU").
  }

  iAssert (⌜forall k, (deqIdx' <= k < tId * Pos.to_nat segment_size)%nat ->
                 ∃ γt th r, l !! k = Some (Some (cellInhabited γt th (Some (cellCancelled r))))⌝)%I as %HCanc.
  {
    repeat rewrite big_sepL_forall.
    iDestruct "HEv''" as %HCanc.
    iPureIntro.
    intros k [HK1 HK2].
    apply nat_le_sum in HK1. destruct HK1 as (v & ->).
    eapply HCanc.
    apply seq_lookup.
    lia.
  }

  assert (tId * Pos.to_nat segment_size <= newDeqFront)%nat.
  {
    destruct (decide (tId * Pos.to_nat segment_size <= newDeqFront)%nat); auto.
    exfalso.
    assert (newDeqFront > 0 ∧ (exists γt th r, l !! (newDeqFront - 1)%nat = Some (Some (cellInhabited γt th (Some (cellCancelled r))))) -> False) as HH by assumption.
    apply HH. split; first by lia.
    apply HCanc.
    lia.
  }
  iSplitR; first done.
  iExists _, _. iFrame "HEnqIt HDeqCounter".
  iSplitL "HDeqLoc".
  {
    iDestruct "HDeqLoc" as (? ? ?) "[H1 H2]".
    iExists _; iSplitR; last by iExists _; iFrame.
    iPureIntro. lia.
  }
  iFrame.
  iSplitL.
  2: by iPureIntro; lia.

  iDestruct "HRest'" as ">HRest'".
  iCombine "HRest' HAwaks" as "HAwaks".
  rewrite -big_sepL_app -seq_app.
  replace (_ + _ + _) with (tId * Pos.to_nat segment_size); first done.
  lia.
Qed.

Lemma iterator_issued_implies_bound γ i:
  iterator_issued γ i -∗
  iterator_counter_at_least γ (S i).
Proof.
  apply own_mono, auth_included; simpl; split; try done.
  apply prod_included'; simpl; split; try done.
  apply ucmra_unit_least.
Qed.

Lemma iterator_counter_at_least_mono γ i j:
  (j <= i)%nat ->
  iterator_counter_at_least γ i -∗
  iterator_counter_at_least γ j.
Proof.
  intros HLe. apply own_mono, auth_included; simpl; split; try done.
  apply prod_included'; simpl; split; try done.
  by apply max_nat_included.
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
