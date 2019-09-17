From iris.heap_lang Require Import notation.

Require Import SegmentQueue.lib.infinite_array.infinite_array_impl.
Require Import SegmentQueue.lib.infinite_array.iterator.
Require Import SegmentQueue.lib.util.getAndSet.
Require Import SegmentQueue.lib.util.interruptibly.

Section impl.

Variable segment_size: positive.

Notation RESUMEDV := (SOMEV #0).
Notation CANCELLEDV := (SOMEV #1).

Definition cancel_cell: val :=
  λ: "cell'",
  let: "cell" := cell_ref_loc "cell'" in
  if: getAndSet "cell" CANCELLEDV = RESUMEDV
  then segment_cancel_single_cell (Fst "cell")
  else #().

Definition move_ptr_forward : val :=
  rec: "loop" "ptr" "seg" := let: "curSeg" := !"ptr" in
                             if: segment_id "seg" ≤ segment_id "curSeg"
                             then #() else
                               if: CAS "ptr" "curSeg" "seg"
                               then #() else "loop" "ptr" "seg".

Definition park: val :=
  λ: "cancellationHandler" "cancHandle" "threadHandle",
  let: "r" := (loop: (λ: "c", ! "c")%V
               interrupted: "cancellationHandler") in
  "threadHandle" <- NONEV ;;
  "r".

Definition unpark: val :=
  λ: "threadHandle", "threadHandle" <- SOMEV #().

Definition suspend: val :=
  λ: "handler" "cancHandle" "threadHandle" "tail" "enqIdx",
  let: "cell'" := (iterator_step segment_size) "tail" "enqIdx" in
  move_ptr_forward "tail" (Fst "cell'") ;;
  let: "cell" := cell_ref_loc "cell'" in
  if: getAndSet "cell" (InjL "threadHandle") = RESUMEDV
  then #()
  else park ("handler" (cancel_cell "cell'")) "cancHandle" "threadHandle".

Definition resume: val :=
  rec: "resume" "head" "deqIdx" :=
    let: "cell'" := (iterator_step_skipping_cancelled segment_size)
                      "head" "deqIdx" in
    segment_cutoff (Fst "cell'") ;;
    move_ptr_forward "head" (Fst "cell'") ;;
    let: "cell" := cell_ref_loc "cell'" in
    let: "p" := getAndSet "cell" RESUMEDV in
    match: "p" with
        InjL "x" => if: "x" = #() then #() else unpark "x"
      | InjR "x" => "resume" "head" "deqIdx"
    end.

Definition new_thread_queue: val :=
  λ: <>, let: "arr" := new_infinite_array segment_size #() in
         let: "hd" := ref "arr" in
         let: "tl" := ref "tl" in
         let: "enqIdx" := ref #0 in
         let: "deqIdx" := ref #0 in
         (("hd", "enqIdx"), ("tl", "deqIdx")).

End impl.

From iris.heap_lang Require Import proofmode.
From iris.algebra Require Import auth.

Section moving_pointers.

Context `{heapG Σ}.

Variable cell_is_processed: nat -> iProp Σ.

Variable segment_size: positive.
Variable ap: @infinite_array_parameters Σ.

Context `{iArrayG Σ}.

Class iArrayPtrG Σ := IArrayPtrG { iarrayptr_inG :> inG Σ (authUR mnatUR) }.
Definition iArrayPtrΣ : gFunctors := #[GFunctor (authUR mnatUR)].
Instance subG_iArrayPtrΣ {Σ} : subG iArrayPtrΣ Σ -> iArrayPtrG Σ.
Proof. solve_inG. Qed.

Context `{iArrayPtrG Σ}.

Definition ptr_points_to_segment γa γ ℓ id :=
  (∃ (ℓ': loc), ℓ ↦ #ℓ' ∗ segment_location γa id ℓ' ∗ own γ (● (id: mnatUR)))%I.

Theorem move_ptr_forward_spec γa γ (v: loc) id ℓ:
  segment_location γa id ℓ -∗
  ([∗ list] j ∈ seq 0 (id * Pos.to_nat segment_size), cell_is_processed j) -∗
  <<< ∀ (id': nat), ▷ is_infinite_array segment_size ap γa ∗
                      ptr_points_to_segment γa γ v id' >>>
    move_ptr_forward #v #ℓ @ ⊤
    <<< ▷ is_infinite_array segment_size ap γa ∗
      ptr_points_to_segment γa γ v (id `max` id'),
  RET #() >>>.
Proof.
  iIntros "#HSegLoc HProc" (Φ) "AU". wp_lam. wp_pures. iLöb as "IH".
  wp_bind (!_)%E.
  iMod "AU" as (id') "[[HIsInf HPtr] [HClose _]]".
  iDestruct "HPtr" as (ℓ') "(Htl & #HLoc & HAuth)".
  wp_load.
  iMod (own_update with "HAuth") as "[HAuth HFrag]".
  { apply auth_update_core_id with (b := id'); try done. apply _. }
  iMod ("HClose" with "[HIsInf Htl HLoc HAuth]") as "AU";
    first by eauto with iFrame.
  iModIntro. wp_pures.
  wp_bind (segment_id #ℓ').

  awp_apply segment_id_spec without "HProc".
  iApply (aacc_aupd_abort with "AU"); first done.
  iIntros (?) "[HIsInf HPtr]".
  iDestruct (is_segment_by_location with "HLoc HIsInf")
    as (? ?) "[HIsSeg HArrRestore]".
  iAaccIntro with "HIsSeg"; iFrame; iIntros "HIsSeg"; iModIntro;
    iDestruct (bi.later_wand with "HArrRestore HIsSeg") as "$".
  by eauto.

  iIntros "AU !> HProc".

  awp_apply segment_id_spec without "HProc".
  iApply (aacc_aupd with "AU"); first done.
  iIntros (id'') "[HIsInf HPtr]".
  iDestruct (is_segment_by_location with "HSegLoc HIsInf")
    as (? ?) "[HIsSeg HArrRestore]".
  iAaccIntro with "HIsSeg"; iFrame; iIntros "HIsSeg"; iModIntro;
    iDestruct (bi.later_wand with "HArrRestore HIsSeg") as "$".
  by eauto.

  destruct (decide (id <= id')) eqn:E.
  {
    iRight. iSplitL.
    { iAssert (⌜id' <= id''⌝)%I with "[HFrag HPtr]" as %HLt.
      { iDestruct "HPtr" as (?) "(_ & _ & HAuth)".
        iDestruct (own_valid_2 with "HAuth HFrag")
          as %[HH%mnat_included _]%auth_both_valid.
        iPureIntro. lia.
      }
      replace (id `max` id'')%nat with id''. done. lia. }
    iIntros "HΦ !> HProc". wp_pures. rewrite bool_decide_decide E. by wp_pures.
  }
  iLeft. iFrame. iIntros "AU !> HProc". wp_pures. rewrite bool_decide_decide E.
  wp_pures.

  wp_bind (CmpXchg _ _ _).
  iMod "AU" as (?) "[[HIsInf HPtr] HClose]".
  iDestruct "HPtr" as (ℓ'') "(Htl & #HLocs & HAuth)".

  destruct (decide (ℓ'' = ℓ')); subst.
  {
    wp_cmpxchg_suc.
    iDestruct (segment_location_id_agree with "HIsInf HLoc HLocs") as %<-.
    iMod (own_update with "HAuth") as "[HAuth _]".
    { apply auth_update_alloc. apply (mnat_local_update _ _ id). lia. }
    iMod ("HClose" with "[HIsInf Htl HAuth]") as "HΦ".
    { rewrite Max.max_l. iFrame. iExists _. by iFrame. lia. }
    iModIntro. by wp_pures.
  }
  {
    wp_cmpxchg_fail.
    iDestruct "HClose" as "[HClose _]".
    iMod ("HClose" with "[HIsInf Htl HAuth]") as "AU";
      first by eauto with iFrame.
    iModIntro. wp_pures. wp_lam. wp_pures.
    iApply ("IH" with "HProc AU").
  }
Qed.

End moving_pointers.

From iris.algebra Require Import list gset excl csum.

Section proof.

Notation iteratorUR := (prodUR (optionUR positiveR) mnatUR).
Notation deqIteratorUR := iteratorUR.
Notation enqIteratorUR := iteratorUR.

Inductive cellTerminalState :=
| cellCancelled
| cellResumed
| cellFilled
| cellAbandoned.

Notation cellProgressUR := mnatUR.
Definition cellUninitializedO: cellProgressUR := 0%nat.
Definition cellInitializedO: cellProgressUR := 1%nat.
Definition cellInhabitedO: cellProgressUR := 2%nat.
Definition cellDoneO: cellProgressUR := 3%nat.

Notation cellStateUR := (prodUR (prodUR cellProgressUR
                                        (optionUR (agreeR cellTerminalState)))
                                (prodUR (optionUR (exclR Qp))
                                        (optionUR (exclR unitO)))).

Notation queueContentsUR := (authUR (listUR cellStateUR)).

Notation enqueueUR := (prodUR (optionUR positiveR) (gset_disjUR nat)).
Notation algebra := enqueueUR.

Class threadQueueG Σ := ThreadQueueG { thread_queue_inG :> inG Σ algebra }.
Definition threadQueueΣ : gFunctors := #[GFunctor algebra].
Instance subG_threadQueueΣ {Σ} : subG threadQueueΣ Σ -> threadQueueG Σ.
Proof. solve_inG. Qed.

Context `{heapG Σ} `{iArrayG Σ} `{iteratorG Σ} (N: namespace).
Notation iProp := (iProp Σ).

Variable segment_size: positive.

Definition cell_invariant (γtq γa: gname) (n: nat) (ℓ: loc): iProp :=
  (cell_cancellation_handle segment_size γa n ∗ ℓ ↦ NONEV ∨
   True
  )%I.

Lemma cell_invariant_persistent:
  forall γtq γ n ℓ, Persistent (inv N (cell_invariant γtq γ n ℓ)).
Proof. apply _. Qed.

Definition tq_ap (γtq γe: gname) :=
  {|
    p_cell_is_done_persistent := iterator_counter_at_least_persistent γe;
    p_cell_invariant_persistent := cell_invariant_persistent γtq;
  |}.

Theorem tq_cell_init γtq γe:
  cell_init segment_size (tq_ap γtq γe) ∅.
Proof.
  rewrite /cell_init /=. iIntros "!>"  (γ id ℓ) "HCancHandle Hℓ".
  iMod (inv_alloc N _ (cell_invariant γtq γ id ℓ) with "[-]") as "#HInv".
  { iModIntro. rewrite /cell_invariant. iLeft; iFrame. }
  iModIntro. iApply "HInv".
Qed.

Theorem filter_app {A} (P: A -> Prop) {H': forall x, Decision (P x)} (l1 l2: list A):
  filter P (l1 ++ l2) = filter P l1 ++ filter P l2.
Proof.
  unfold filter. induction l1; rewrite /= // /filter. rewrite IHl1.
  by destruct (decide (P a)).
Qed.

Theorem filter_List_filter_compatible {A} (P: A -> bool) (l: list A):
  filter P l = List.filter P l.
Proof.
  rewrite /filter. induction l; rewrite /= //.
  rewrite -IHl. by destruct (P a).
Qed.

Definition count_matching {A} (P: A -> Prop) {H': forall x, Decision (P x)} (l: list A): nat :=
  length (filter P l).

Hint Unfold count_matching.

Theorem count_matching_app {A} (P: A -> Prop) {H': forall x, Decision (P x)} (l1 l2: list A):
  count_matching P (l1 ++ l2) = (count_matching P l1 + count_matching P l2)%nat.
Proof. by rewrite /count_matching filter_app app_length. Qed.

Theorem count_matching_is_sum
        {A} (P: A -> Prop) {H': forall x, Decision (P x)}:
  forall l,
  let to_nat x := if decide (P x) then 1%nat else 0%nat in
  count_matching P l = foldr (fun v a => a + to_nat v)%nat O l.
Proof.
  rewrite /count_matching /filter. induction l; rewrite /= //.
  destruct (decide (P a)); rewrite /= IHl /=; lia.
Qed.

Theorem count_matching_alter
        {A} (P: A -> Prop) {H': forall x, Decision (P x)}:
  let to_num x := if decide (P x) then 1%nat else 0%nat in
  forall v f l i, l !! i = Some v ->
               count_matching P (alter f i l) =
               (count_matching P l - (to_num v) + (to_num (f v)))%nat.
Proof.
  rewrite /count_matching /alter /filter. induction l; rewrite /= //.
  case; rewrite /=.
  { intros. simplify_eq. destruct (decide (P v)); destruct (decide (P (f v))).
    all: rewrite /=; lia. }
  intros n Hel. rewrite /filter /=. destruct (decide (P a)); rewrite /= IHl //.
  destruct (decide (P v)) as [pv|]; simpl. 2: lia.
  destruct (list_filter P H' l) eqn:Z.
  2: destruct (decide (P (f v))); simpl; lia.
  exfalso.
  revert n Z Hel pv. clear. induction l.
  - intros. inversion Hel.
  - intros. destruct n.
    * inversion Hel. subst. simpl in *. destruct (decide (P v)); done.
    * inversion Hel. eapply IHl; try done. simpl in *.
      by destruct (decide (P a)).
Qed.

Inductive cellState :=
| cellInitialized
| cellInhabited
| cellDone: cellTerminalState -> cellState.

Definition cellStateProgress (k: option cellState): cellProgressUR :=
  match k with
  | None => cellUninitializedO
  | Some cellInitialized => cellInitializedO
  | Some cellInhabited => cellInhabitedO
  | Some (cellDone _) => cellDoneO
  end.

(* The cell is not part of the queue any longer. *)
Definition wasRemoved (k: option cellState): bool :=
  match k with
  | Some (cellDone _) => true
  | _ => false
  end.

Definition is_thread_queue (S R: iProp) γa γtq γe γd eℓ epℓ dℓ dpℓ :=
  let ap := tq_ap γtq γe in
  (is_infinite_array segment_size ap γa ∗
   ∃ (enqIdx deqIdx: nat),
   iterator_points_to segment_size γa γe eℓ epℓ enqIdx ∗
   iterator_points_to segment_size γa γd dℓ dpℓ deqIdx ∗
   ∃ (enqFront deqFront: nat) (l: list (option cellState)),
     ⌜deqIdx <= deqFront⌝ ∧ ⌜enqIdx <= enqFront⌝ ∧
     ⌜deqFront <= enqFront < length l⌝ ∧
     ([∗ list] i ↦ k ∈ take enqFront l, if wasRemoved k then True else S)%I ∗
     ([∗ list] i ↦ k ∈ take deqFront l, if wasRemoved k then True else R)%I ∗
     ([∗ list] i ↦ k ∈ l,
      match k with
      | None => True
      | Some cellState => ∃ ℓ, array_mapsto segment_size γa i ℓ ∗
          match cellState with
          | cellInitialized => ℓ ↦ NONEV ∗ cell_cancellation_handle segment_size γa i
          | cellInhabited => (∃ (th: val), ℓ ↦ InjLV th ∗ iterator_issued γe i)
          | cellDone cd => ℓ ↦ - ∗ match cd with
                          | cellAbandoned => (iterator_issued γd i ∨ S)
                          | cellCancelled => True
                          | cellResumed => (cell_cancellation_handle segment_size γa i ∨ R)
                          | cellFilled => (iterator_issued γe i ∨ R)
                          end
          end
      end)
  )%I.

End proof.
