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

Notation cellProgressUR := mnatUR (only parsing).
Definition cellUninitializedO: cellProgressUR := 0%nat.
Definition cellInitializedO: cellProgressUR := 1%nat.
Definition cellInhabitedO: cellProgressUR := 2%nat.
Definition cellDoneO: cellProgressUR := 3%nat.

Canonical Structure cellTerminalStateO := leibnizO cellTerminalState.

Notation cellStateUR := (prodUR cellProgressUR
                                (optionUR (agreeR cellTerminalStateO))).

Notation queueContentsUR := (listUR cellStateUR).

Notation enqueueUR := (optionUR positiveR).
Notation dequeueUR := (prodUR (optionUR positiveR) mnatUR).
Notation algebra := (authUR (prodUR (prodUR enqueueUR dequeueUR) queueContentsUR)).

Class threadQueueG Σ := ThreadQueueG { thread_queue_inG :> inG Σ algebra }.
Definition threadQueueΣ : gFunctors := #[GFunctor algebra].
Instance subG_threadQueueΣ {Σ} : subG threadQueueΣ Σ -> threadQueueG Σ.
Proof. solve_inG. Qed.

Context `{heapG Σ} `{iArrayG Σ} `{iteratorG Σ} `{threadQueueG Σ} (N: namespace).
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

(* The cell is still present in the queue. *)
Definition still_present (k: option cellState): bool :=
  match k with
  | Some (cellDone _) => false
  | _ => true
  end.

Definition cell_state_to_RA (k: option cellState) :=
  match k with
    | None => (cellUninitializedO, None)
    | Some s => match s with
               | cellInitialized => (cellInitializedO, None)
               | cellInhabited => (cellInhabitedO, None)
               | cellDone d => (cellDoneO, Some (to_agree d))
               end
  end.

Definition cell_resources S R γa γe γd i k :=
  (match k with
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
  end)%I.

Definition cell_list_contents (S R: iProp) γa γtq γe γd
           (l: list (option cellState)) (deqFront: nat): iProp :=
  (let nEnq := (count_matching still_present l)%nat in
   let nDeq := (count_matching still_present (take deqFront l))%nat in
   ⌜deqFront <= length l⌝ ∗
   own γtq (● (((if Nat.ltb O nEnq then Some (Pos.of_nat nEnq) else None),
                (if Nat.ltb O nDeq then Some (Pos.of_nat nDeq) else None,
                  deqFront: mnatUR)),
               map cell_state_to_RA l)) ∗
       ([∗ list] s ∈ replicate nEnq S, s) ∗ ([∗ list] r ∈ replicate nDeq R, r) ∗
       ([∗ list] i ↦ k ∈ l, cell_resources S R γa γe γd i k))%I.

Lemma cell_list_contents_append S R γa γtq γe γd l deqFront:
  S -∗ cell_list_contents S R γa γtq γe γd l deqFront ==∗
  own γtq (◯ (Some (1%positive), ε, replicate (length l) ε ++ [ε])) ∗
  cell_list_contents S R γa γtq γe γd (l ++ [None]) deqFront.
Proof.
  iIntros "HS (% & HAuth & HSs & HRs & HCellResources)".
  iMod (own_update with "HAuth") as "[HAuth HFrag]".
  2: {
    iFrame "HFrag". iSplitR.
    { iPureIntro. rewrite app_length. lia. }
    replace (take deqFront (l ++ [None])) with (take deqFront l).
    2: by rewrite take_app_le; [done|lia].

    iFrame "HAuth".
    rewrite count_matching_app replicate_plus big_sepL_app /=; iFrame.
    simpl. done.
  }

  apply auth_update_alloc.
  apply prod_local_update'.
  apply prod_local_update_1.
  rewrite count_matching_app.
  remember (count_matching _ l) as K.
  destruct K. apply alloc_option_local_update; done.
  rewrite Nat2Pos.inj_add; auto. rewrite /= /count_matching /=.
  apply local_update_unital_discrete. intros ? _ HEq.
  split. done. by rewrite Pos.add_comm Some_op HEq ucmra_unit_left_id.

  rewrite map_app. simpl.
  replace (length l) with (length (map cell_state_to_RA l)).
  apply list_append_local_update. intros.
  apply list_lookup_validN. simpl. destruct i; done.
  by rewrite map_length.
Qed.

Fixpoint find_index' {A} (P: A -> Prop) {H': forall x, Decision (P x)}
         (l: list A) (i: nat): option nat :=
  match l with
  | nil => None
  | cons x l => if decide (P x) then Some i else find_index' P l (S i)
  end.

Definition find_index {A} (P: A -> Prop) {H': forall x, Decision (P x)}
           (l: list A): option nat := find_index' P l O.

Lemma find_index_Some {A} (P: A -> Prop) {H': forall x, Decision (P x)}:
  forall l i, find_index P l = Some i ->
         (exists v, l !! i = Some v /\ P v) /\
         (forall i', (i' < i)%nat -> exists v', l !! i' = Some v' /\ not (P v')).
Proof.
  rewrite /find_index /=. remember O as start. intros ? ?.
  replace (Some i) with (Some (start + i))%nat. 2: congr Some; lia.
  clear Heqstart.
  revert i. revert start.
  induction l; intros ? ? HIsSome; first by inversion HIsSome.
  destruct i; simpl in *.
  {
    rewrite Nat.add_0_r in HIsSome.
    destruct (decide (P a)).
    { split. eexists _. done. intros ? HContra. inversion HContra. }
    exfalso. revert HIsSome. clear. change (S start) with (1 + start)%nat.
    remember 0%nat as K. clear HeqK. revert K.
    induction l; intros ? HContra; inversion HContra as [HContra'].
    destruct (decide (P a)).
    - inversion HContra' as [H]. lia.
    - by apply (IHl (S K)).
  }
  destruct (decide (P a)) as [p|p]. inversion HIsSome; lia.
  destruct (IHl (S start) i) as [HH HH']. by rewrite HIsSome; congr Some; lia.
  split; first done.
  intros i' HLt. inversion HLt; subst.
  { destruct i; eauto. }
  destruct i'; eauto. simpl.
  apply HH'. lia.
Qed.

Lemma find_index_None {A} (P: A -> Prop) {H': forall x, Decision (P x)}:
  forall l, find_index P l = None -> forall v, In v l -> not (P v).
Proof.
  unfold find_index. remember O as start. clear Heqstart.
  intros l HIsNone v HIn. generalize dependent start.
  induction l; intros start HIsNone; first by inversion HIn.
  simpl in *; destruct (decide (P a)); first by discriminate.
  inversion HIn; subst; eauto.
Qed.

Lemma cell_list_contents_register_for_dequeue E R γa γtq γe γd l deqFront:
  forall i, find_index still_present (drop deqFront l) = Some i ->
  R -∗ cell_list_contents E R γa γtq γe γd l deqFront ==∗
  own γtq (◯ (ε, (Some (1%positive), (deqFront + S i)%nat: mnatUR), ε)) ∗
  cell_list_contents E R γa γtq γe γd l (deqFront + S i)%nat.
Proof.
  iIntros (i HFindSome) "HR (% & HAuth & HSs & HRs & HCellResources)".

  apply find_index_Some in HFindSome.
  destruct HFindSome as [[v [HIn HPresent]] HNotPresent].
  assert (i < length (drop deqFront l))%nat as HLt.
  { apply lookup_lt_is_Some. by eexists. }

  assert (S (count_matching still_present (take deqFront l)) =
              count_matching still_present (take (deqFront + S i) l)) as HCountMatching.
  {
    replace (take (deqFront + S i) l) with
        (take (deqFront + S i) (take deqFront l ++ drop deqFront l)).
    2: by rewrite take_drop.
    rewrite take_plus_app.
    2: rewrite take_length_le; lia. rewrite count_matching_app.
    replace (count_matching still_present (take (S i) (drop deqFront l))) with 1%nat.
    by lia.

    remember (drop deqFront l) as l'.
    replace l' with (take i l' ++ v :: drop (S i) l').
    2: by rewrite take_drop_middle.

    replace (S i) with (i + 1)%nat by lia.

    rewrite take_plus_app. 2: rewrite take_length_le; [done|lia].
    rewrite count_matching_app. simpl.
    assert (count_matching still_present (take i l') = 0%nat) as ->. {
      assert (forall i', (i' < i)%nat -> exists v', take i l' !! i' = Some v' /\
                                         not (still_present v')) as HH.
      {
        intros i' HLti'. destruct (HNotPresent i' HLti')
          as [v' [HEl Hv'NotPresent]].
        exists v'. split; try done. by rewrite lookup_take.
      }
      remember (take i l') as l''. assert (i = length l'') as HLen.
      by subst; rewrite take_length_le; lia.
      subst i.
      revert HH. clear. rewrite /count_matching /filter /=.
      induction l''; auto=> H. simpl in *.
      destruct (H O) as [p H']; simpl in *; first by lia.
      destruct H' as [[=] HH]; subst. destruct (decide (still_present p)).

      contradiction.
      apply IHl''.
      intros i' HLt.
      destruct (H (S i')); first by lia.
      simpl in *. eauto.
    }
    by rewrite /count_matching /filter /= decide_left /=.
  }

  iMod (own_update with "HAuth") as "[HAuth HFrag]".
  2: {
    iFrame "HFrag". iSplitR.
    { iPureIntro. rewrite drop_length in HLt. lia. }
    iFrame. rewrite -HCountMatching. simpl. by iFrame.
  }

  rewrite -HCountMatching.

  apply auth_update_alloc.
  apply prod_local_update_1. apply prod_local_update_2. apply prod_local_update'.
  remember (count_matching _ _) as K; simpl. clear.
  destruct K; simpl.
  by apply alloc_option_local_update.
  {
    apply local_update_unital_discrete. intros ? _ HEq.
    split. done. replace (S (S K)) with (1 + S K)%nat by lia.
    rewrite Nat2Pos.inj_add; auto. by rewrite Some_op HEq ucmra_unit_left_id.
  }
  apply mnat_local_update. lia.
Qed.

Definition is_thread_queue (S R: iProp) γa γtq γe γd eℓ epℓ dℓ dpℓ :=
  let ap := tq_ap γtq γe in
  (is_infinite_array segment_size ap γa ∗
   ∃ (enqIdx deqIdx: nat),
   iterator_points_to segment_size γa γe eℓ epℓ enqIdx ∗
   iterator_points_to segment_size γa γd dℓ dpℓ deqIdx ∗
   ∃ (deqFront: nat) (l: list (option cellState)),
   ⌜deqIdx <= deqFront <= length l⌝ ∧ ⌜enqIdx <= length l⌝
  )%I.

End proof.
