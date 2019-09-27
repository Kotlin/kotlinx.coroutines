From iris.heap_lang Require Import notation.

Require Import SegmentQueue.lib.infinite_array.infinite_array_impl.
Require Import SegmentQueue.lib.infinite_array.iterator.
Require Import SegmentQueue.lib.util.getAndSet.
Require Import SegmentQueue.lib.util.interruptibly.

Notation RESUMEDV := (SOMEV #0).
Notation CANCELLEDV := (SOMEV #1).

Section impl.

Variable segment_size: positive.

Definition cancel_cell: val :=
  λ: "cell'",
  let: "cell" := cell_ref_loc "cell'" in
  if: getAndSet "cell" CANCELLEDV = RESUMEDV
  then #false
  else segment_cancel_single_cell (Fst "cell") ;; #true.

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
  "threadHandle" <- #true ;;
  "r".

Definition unpark: val :=
  λ: "threadHandle", "threadHandle" <- #false.

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

Section parking.

Notation algebra := (authUR (optionUR
                               (prodR fracR (agreeR boolO)))).

Class parkingG Σ := ParkingG { parking_inG :> inG Σ algebra }.
Definition parkingΣ : gFunctors := #[GFunctor algebra].
Instance subG_parkingΣ {Σ} : subG parkingΣ Σ -> parkingG Σ.
Proof. solve_inG. Qed.

Context `{heapG Σ} `{parkingG Σ} `{interruptiblyG Σ}.

Definition thread_handle_in_state (γ: gname) (v: loc) (x: bool): iProp Σ :=
  (v ↦ #x ∗ own γ (● (Some (1%Qp, to_agree x))))%I.

Definition is_thread_handle (γ: gname) (v: val) :=
  (∃ (ℓ: loc) x, ⌜v = #ℓ⌝ ∗ thread_handle_in_state γ ℓ x)%I.

Definition thread_handler (γ: gname) (q: Qp) (x: bool): iProp Σ :=
  own γ (◯ (Some (q, to_agree x))).

Theorem thread_update_state γ (ℓ: loc) (x'': bool):
  <<< ∀ x', ▷ is_thread_handle γ #ℓ ∗ ▷ thread_handler γ 1 x' >>>
    #ℓ <- #x'' @ ⊤
  <<< thread_handle_in_state γ ℓ x'' ∗ thread_handler γ 1 x'', RET #() >>>.
Proof.
  iIntros (Φ) "AU".
  iMod "AU" as (x') "[[HIsHandle HFrag] [_ HClose]]".
  iDestruct "HIsHandle" as (? ?) "[>% [HLoc HAuth]]". simplify_eq.
  wp_store.
  iMod (own_update_2 with "HAuth HFrag") as "[HAuth HFrag]".
  { by apply auth_update, option_local_update,
      (exclusive_local_update _ (1%Qp, to_agree x'')). }
  iMod ("HClose" with "[HLoc HAuth HFrag]") as "HΦ".
  by iFrame.
  by iModIntro.
Qed.

Definition thread_has_permit γ := thread_handler γ 1 false.
Definition thread_doesnt_have_permits γ := thread_handler γ 1 true.

Theorem unpark_spec γ (ℓ: loc):
  <<< ▷ is_thread_handle γ #ℓ ∗ ▷ thread_doesnt_have_permits γ >>>
      unpark #ℓ @ ⊤
  <<< thread_handle_in_state γ ℓ false ∗ thread_has_permit γ, RET #() >>>.
Proof.
  iIntros (Φ) "AU". wp_lam.
  awp_apply thread_update_state. iApply (aacc_aupd_commit with "AU"); first done.
  iIntros "H".
  iAaccIntro with "H"; first by iIntros "[$ $] !> AU".
  by iIntros "[$ $] !> $ !>".
Qed.

End parking.

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
| cellAbandoned.

Notation cellProgressUR := mnatUR (only parsing).
Notation cellUninitializedO := (0%nat: mnatUR) (only parsing).
Notation cellInitializedO := (1%nat: mnatUR) (only parsing).
Notation cellInhabitedO := (2%nat: mnatUR) (only parsing).
Notation cellDoneO := (3%nat: mnatUR) (only parsing).

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

Definition rendezvous_state γtq i (r: cellStateUR) :=
  own γtq (◯ (ε, replicate i ε ++ [r])).

Definition rendezvous_resumed (γtq: gname) (i: nat): iProp :=
  rendezvous_state γtq i (ε, Some (to_agree cellResumed)).
Definition rendezvous_cancelled (γtq: gname) (i: nat): iProp :=
  rendezvous_state γtq i (ε, Some (to_agree cellCancelled)).
Definition rendezvous_initialized γtq i :=
  rendezvous_state γtq i (cellInitializedO, ε).
Definition rendezvous_inhabited γtq i :=
  rendezvous_state γtq i (cellInhabitedO, ε).

Definition cell_invariant (γtq γa: gname) (n: nat) (ℓ: loc): iProp :=
  (cell_cancellation_handle segment_size γa n ∗ ℓ ↦ NONEV ∨
   rendezvous_initialized γtq n)%I.

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

Fixpoint count_matching {A} (P: A -> Prop) {H': forall x, Decision (P x)} (l: list A): nat :=
  match l with
  | nil => 0
  | cons x l' => if decide (P x) then S (count_matching P l') else count_matching P l'
  end.

Theorem count_matching_is_length_filter {A} (P: A -> Prop) {H': forall x, Decision (P x)} l:
  count_matching P l = length (filter P l).
Proof.
  induction l; auto.
  simpl. unfold filter in *. simpl.
  destruct (decide (P a)); simpl; auto.
Qed.

Theorem count_matching_app {A} (P: A -> Prop) {H': forall x, Decision (P x)} (l1 l2: list A):
  count_matching P (l1 ++ l2) = (count_matching P l1 + count_matching P l2)%nat.
Proof. repeat rewrite count_matching_is_length_filter.
         by rewrite filter_app app_length. Qed.

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
  induction l; rewrite /= //; unfold to_num in *.
  case; rewrite /=.
  { intros. simplify_eq. destruct (decide (P v)); destruct (decide (P (f v))).
    all: rewrite /=; lia. }
  intros n Hel. rewrite /filter /=. destruct (decide (P a)); rewrite /= IHl //.
  destruct (decide (P v)) as [pv|]; simpl. 2: lia.
  destruct (count_matching P l) eqn:Z.
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
| cellInhabited
| cellDone: cellTerminalState -> cellState.

Definition cellStateProgress (k: option cellState): cellProgressUR :=
  match k with
  | None => cellUninitializedO
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
               | cellInhabited => (cellInhabitedO, None)
               | cellDone d => (cellDoneO, Some (to_agree d))
               end
  end.

Definition cell_resources S R γa γe γd i k :=
  (match k with
   | None => True
   | Some cellState => ∃ ℓ, array_mapsto segment_size γa i ℓ ∗
        match cellState with
        | cellInhabited => (∃ (th: val), ℓ ↦ InjLV th)
                            ∗ iterator_issued γe i
                            ∗ cell_cancellation_handle segment_size γa i
        | cellDone cd => match cd with
          | cellAbandoned => cell_cancellation_handle segment_size γa i ∗
                            iterator_issued γe i ∗
                            (iterator_issued γd i ∨ (∃ th, ℓ ↦ InjLV th) ∗ S)
          | cellCancelled => iterator_issued γe i ∗ (ℓ ↦ CANCELLEDV ∨ ℓ ↦ RESUMEDV)
          | cellResumed => iterator_issued γd i ∗
                          cell_cancellation_handle segment_size γa i ∗
                           (iterator_issued γe i ∨ ℓ ↦ RESUMEDV ∗ R)
          end
        end
  end)%I.

Theorem cell_resources_timeless S R γa γe γd i k :
  Timeless R -> Timeless S ->
  Timeless (cell_resources S R γa γe γd i k).
Proof. destruct k; try apply _. destruct c; try apply _.
       destruct c; apply _.
Qed.

Definition cell_list_contents_auth_ra nDeq l deqFront :=
   ((match l with | [] => None | _ => Some (Pos.of_nat (length l)) end,
                (if Nat.ltb O nDeq then Some (Pos.of_nat nDeq) else None,
                  deqFront: mnatUR)),
               map cell_state_to_RA l).

Definition cell_list_contents (S R: iProp) γa γtq γe γd
           (l: list (option cellState)) (deqFront: nat): iProp :=
  (let nEnq := (count_matching still_present l)%nat in
   let nDeq := (count_matching still_present (take deqFront l))%nat in
   ⌜deqFront <= length l⌝ ∗
   own γtq (● cell_list_contents_auth_ra nDeq l deqFront) ∗
       ([∗ list] s ∈ replicate nEnq S, s) ∗ ([∗ list] r ∈ replicate nDeq R, r) ∗
       ([∗ list] i ↦ k ∈ l, cell_resources S R γa γe γd i k))%I.

Definition suspension_permit γtq := own γtq (◯ (Some (1%positive), ε, ε)).

Definition exists_list_element γtq (n: nat) :=
  own γtq (◯ (ε, replicate n ε ++ [ε])).

Lemma cell_list_contents_append E R γa γtq γe γd l deqFront:
  E -∗ cell_list_contents E R γa γtq γe γd l deqFront ==∗
  (suspension_permit γtq ∗
  exists_list_element γtq (length l)) ∗
  cell_list_contents E R γa γtq γe γd (l ++ [None]) deqFront.
Proof.
  rewrite /suspension_permit -own_op -auth_frag_op
    -pair_op ucmra_unit_left_id ucmra_unit_right_id.
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
  destruct l; simpl; first by apply alloc_option_local_update.
  rewrite app_length Nat.add_comm /=.
  apply local_update_unital_discrete. intros ? _ HEq.
  split. done. change (S (S (length l))) with (1 + S (length l))%nat.
  by rewrite Nat2Pos.inj_add // Some_op HEq ucmra_unit_left_id.

  rewrite map_app.
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

Lemma option_local_update' {A: ucmraT} (x x' y': A):
  (x, ε) ~l~> (x', y') -> (Some x, ε) ~l~> (Some x', Some y').
Proof.
  intros HOld. apply local_update_unital. intros ? ?.
  rewrite ucmra_unit_left_id => HValid HEq. rewrite -HEq.
  destruct (HOld n (Some x)); rewrite /= //.
  by rewrite ucmra_unit_left_id.
  simpl in *. split; try done. rewrite -Some_op. by constructor.
Qed.

Lemma option_local_update'' {A: cmraT} (x y: A):
  (forall n, ✓{n} x -> ✓{n} (y ⋅ x)) ->
  (Some x, ε) ~l~> (Some (y ⋅ x), Some y).
Proof.
  intros HValidYX. apply local_update_unital.
  intros ? ? HValid'. rewrite ucmra_unit_left_id.
  intros <-. rewrite -Some_op. split; try done.
  apply Some_validN. auto.
Qed.

Definition awakening_permit γtq := own γtq (◯ (ε, (Some (1%positive), ε), ε)).

Definition deq_front_at_least γtq (n: nat) :=
  own γtq (◯ (ε, (ε, n: mnatUR), ε)).

Lemma cell_list_contents_register_for_dequeue E R γa γtq γe γd l deqFront:
  forall i, find_index still_present (drop deqFront l) = Some i ->
  R -∗ cell_list_contents E R γa γtq γe γd l deqFront ==∗
  (awakening_permit γtq ∗ deq_front_at_least γtq (deqFront + S i)%nat) ∗
  cell_list_contents E R γa γtq γe γd l (deqFront + S i)%nat.
Proof.
  rewrite /awakening_permit /deq_front_at_least.
  iIntros (i HFindSome) "HR (% & HAuth & HSs & HRs & HCellResources)".
  rewrite -own_op -auth_frag_op.
  repeat rewrite -pair_op ucmra_unit_left_id. rewrite ucmra_unit_right_id.

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

  apply auth_update_alloc.
  apply prod_local_update_1. apply prod_local_update_2. apply prod_local_update'.
  rewrite -HCountMatching.
  remember (count_matching still_present (take deqFront l)) as K.
  {
    destruct K; simpl.
    by apply alloc_option_local_update. change (S (S K)) with (1 + S K)%nat.
    rewrite Nat2Pos.inj_add // Some_op.
    by apply option_local_update''.
  }
  apply mnat_local_update. lia.
Qed.

Definition is_thread_queue (S R: iProp) γa γtq γe γd eℓ epℓ dℓ dpℓ l deqFront :=
  let ap := tq_ap γtq γe in
  (is_infinite_array segment_size ap γa ∗
   cell_list_contents S R γa γtq γe γd l deqFront ∗
   ∃ (enqIdx deqIdx: nat),
   iterator_points_to segment_size γa γe eℓ epℓ enqIdx ∗
   iterator_points_to segment_size γa γd dℓ dpℓ deqIdx ∗
   ([∗ list] i ∈ seq 0 deqIdx,
    awakening_permit γtq ∨ rendezvous_resumed γtq i ∨
    iterator_issued γd i ∗ rendezvous_cancelled γtq i) ∗
   ⌜deqIdx <= deqFront <= length l⌝ ∧ ⌜enqIdx <= length l⌝
  )%I.

Definition is_cell_pointer' γa (ix ic: nat) (v: val) :=
  (∃ (ℓ: loc), segment_location γa ix ℓ ∗ ⌜v = (#ℓ, #ic)%V⌝)%I.

Definition is_cell_pointer γa i v :=
  ias_cell_info_view segment_size (fun ix ic => is_cell_pointer' γa ix ic v) i.

Theorem is_cell_pointer'_persistent γa ix ic v:
  Persistent (is_cell_pointer' γa ix ic v).
Proof. apply _. Qed.

Lemma cell_list_contents_lookup_acc i E R γa γtq γe γd l deqFront:
  cell_list_contents E R γa γtq γe γd l deqFront -∗
  cell_resources E R γa γe γd i (mjoin (l !! i)) ∗
  (cell_resources E R γa γe γd i (mjoin (l !! i)) -∗
   cell_list_contents E R γa γtq γe γd l deqFront).
Proof.
  iIntros "(% & HAuth & HEs & HRs & HCellResources)".
  destruct (l !! i) eqn:X; simpl.
  2: by iFrame.
  iDestruct (big_sepL_lookup_acc with "HCellResources")
    as "[HCellResource HListRestore]"; first eassumption.
  iFrame. iIntros "HCellResource". iSplitR. done.
  by iApply "HListRestore".
Qed.

Lemma big_sepL_lookup_alter {A: Type} i s f (P: nat -> A -> iProp) (l: list A) v:
  l !! i = Some v ->
  ([∗ list] i ↦ k ∈ l, P (s+i)%nat k) -∗
  (P (s+i)%nat v ∗ (P (s+i)%nat (f v) -∗
                      [∗ list] i ↦ k ∈ (alter f i l), P (s+i)%nat k)).
Proof.
  iIntros (HEl) "HList".
  iInduction l as [|x l'] "IH" forall (s i HEl); first by inversion HEl.
  destruct i; simpl in *.
  - inversion HEl; subst.
    rewrite Nat.add_0_r. iDestruct "HList" as "[$ $]".
    by iIntros "$".
  - iDestruct "HList" as "[$ HList]".
    rewrite -plus_n_Sm.
    iDestruct ("IH" $! (S s) i HEl with "[HList]") as "[$ HLst] /=".
    { iDestruct (big_sepL_mono with "HList") as "$".
      iIntros (? ? ?) "HAp". by rewrite -plus_n_Sm. }
    iIntros "HPs". iDestruct ("HLst" with "HPs") as "HLst".
    iDestruct (big_sepL_mono with "HLst") as "$".
    iIntros (? ? ?) "HAp". by rewrite -plus_n_Sm.
Qed.

Lemma cell_resources_conflict_invariant E R γa γe γd i c ptr:
  cell_resources E R γa γe γd i (Some c) -∗
  array_mapsto segment_size γa i ptr -∗
  cell_cancellation_handle segment_size γa i -∗
  ptr ↦ - -∗ False.
Proof.
  iIntros "HCellResources #HArrMapsto HCancHandle HPtr".
  simpl.
  iDestruct "HCellResources" as (?) "[#HArrMapsto' HR]".
  iDestruct (array_mapsto_agree with "HArrMapsto' HArrMapsto") as "->".
  iAssert ((∃ q, ptr ↦{q} -) -∗ False)%I with "[HPtr]" as "HContra".
  {
    iIntros "HPtr'".
    iDestruct "HPtr" as (?) "HPtr". iDestruct "HPtr'" as (? ?) "HPtr'".
    iDestruct (mapsto_valid_2 with "HPtr HPtr'") as %HContra.
    exfalso.
    move: HContra. rewrite frac_valid'.
    apply Qp_not_plus_q_ge_1.
  }
  destruct c.
  - iDestruct "HR" as "(HR & _)".
    iDestruct "HR" as (?) "(HR & _)".
    iApply "HContra". eauto.
  - destruct c.
    * iDestruct "HR" as "(_ & [HPtr'|HPtr'])"; iApply "HContra"; eauto.
    * iDestruct "HR" as "(_ & HCancHandle' & _)".
      iApply (cell_cancellation_handle'_exclusive with "HCancHandle HCancHandle'").
    * iDestruct "HR" as "(HCancHandle' & _)".
      iApply (cell_cancellation_handle'_exclusive with "HCancHandle HCancHandle'").
Qed.

Lemma enquirer_not_present_means_filled_if_initialized
      E R γtq γa γe γd i c v l d:
  l !! i = Some c ->
  cell_resources E R γa γe γd i c -∗
  own γtq (● cell_list_contents_auth_ra v l d) -∗
  rendezvous_initialized γtq i -∗
  iterator_issued γe i -∗
  ⌜c = Some (cellDone cellResumed)⌝.
Proof.
  iIntros (HIsSome) "HCellRes HAuth HCellInit HIsSus".
  destruct c.
  2: {
    simpl.
    iDestruct (own_valid_2 with "HAuth HCellInit") as
        %[[_ HContra]%prod_included _]%auth_both_valid.
    exfalso.
    move: HContra. rewrite list_lookup_included.
    intros HContra. specialize (HContra i). simpl in *.
    revert HContra.
    revert HIsSome. clear. revert i. induction l. done.
    case; simpl in *; auto.
    intros HH. simplify_eq.
    rewrite /= Some_included prod_included /=. case.
    by case.
    case; rewrite mnat_included; lia.
  }
  destruct c; simpl.
  {
    iDestruct "HCellRes" as (?) "(_ & _ & HIsSus' & _)".
    iDestruct (iterator_issued_exclusive with "HIsSus HIsSus'") as %[].
  }
  destruct c; simpl; auto; iExFalso.
  1: iDestruct "HCellRes" as (?) "(_ & HIsSus' & _)".
  2: iDestruct "HCellRes" as (?) "(_ & _ & HIsSus' & _)".
  all: iDestruct (iterator_issued_exclusive with "HIsSus HIsSus'") as %[].
Qed.

Lemma None_op_left_id {A: cmraT} (a: option A): None ⋅ a = a.
Proof. rewrite /op /cmra_op /=. by destruct a. Qed.

Theorem inhabit_cell_spec N' E R γa γtq γe γd i ptr th:
  iterator_issued γe i -∗
  exists_list_element γtq i -∗
  array_mapsto segment_size γa i ptr -∗
  inv N' (cell_invariant γtq γa i ptr) -∗
  <<< ∀ l deqFront, ▷ cell_list_contents E R γa γtq γe γd l deqFront >>>
    getAndSet #ptr (InjLV th) @ ⊤ ∖ ↑N'
  <<< ∃ r, ⌜l !! i = Some None⌝ ∧
           ⌜r = InjLV #()⌝ ∧
           ▷ cell_list_contents E R γa γtq γe γd
             (alter (fun _ => Some cellInhabited) i l) deqFront ∨
           ⌜l !! i = Some (Some (cellDone cellResumed))⌝ ∧
           ⌜r = RESUMEDV⌝ ∧
           ▷ R ∗
           ▷ cell_list_contents E R γa γtq γe γd l deqFront , RET r >>>.
Proof.
  iIntros "HIsSus #HExistsEl #HArrMapsto #HCellInv" (Φ) "AU".
  awp_apply getAndSet_spec.

  iAssert (∀ v l d, own γtq (● (cell_list_contents_auth_ra v l d))
                        -∗ ⌜(i < length l)%nat⌝)%I as "HIsLess".
  {
    iIntros (v l d) "HAuth".
    iDestruct (own_valid_2 with "HAuth HExistsEl")
      as %[[_ HH]%prod_included _]%auth_both_valid.
    simpl in *. iPureIntro.
    revert HH. rewrite list_lookup_included=> HH.
    specialize (HH i). move: HH. rewrite option_included.
    case. intros HH; exfalso; by induction i.
    intros (a & b & _ & HH & _).
    replace (length l) with (length (map cell_state_to_RA l)).
    by apply lookup_lt_is_Some; eexists.
    by rewrite map_length.
  }

  iInv N' as "[[>HCancHandle >Hℓ]|>#HCellInit]".
  { (* The cell wasn't in the list, so the resumer has not yet arrived. *)
    iAssert (▷ ptr ↦ InjLV #() ∧ ⌜val_is_unboxed (InjLV #())⌝)%I with "[Hℓ]" as "HAacc".
    by iFrame.

    iAaccIntro with "HAacc".
    { iFrame. unfold cell_invariant. iIntros "[? _]".
      iLeft. iFrame. done. }
    iIntros "Hℓ".

    iMod "AU" as (l deqFront) "[(>% & >HAuth & HEs & HRs & HCellRRs) [_ HClose]]".
    iDestruct ("HIsLess" with "HAuth") as %HIsLess.
    apply lookup_lt_is_Some in HIsLess. destruct HIsLess as [cr HIsSome].
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
    iDestruct (big_sepL_lookup_alter i O (fun _ => Some cellInhabited)) as "HH".
    done.
    simpl; iSpecialize ("HH" with "HCellRRs").
    iDestruct "HH" as "[_ HH]".
    iSpecialize ("HH" with "[HIsSus Hℓ HCancHandle]").
    { iFrame. iExists _. iFrame "HArrMapsto". eauto. }
    remember (alter (fun _ => Some cellInhabited) i l) as l'.
    assert (length l = length l') as HSameLength.
    { subst. by rewrite alter_length. }
    assert (forall n, count_matching still_present (take n l) =
                 count_matching still_present (take n l')) as HCMl'.
    {
      subst. revert HIsSome. clear. move: i. induction l; first done.
      case; simpl. intros [=]; subst; case; done.
      intros ? ?. case; simpl; first done.
      destruct (decide (still_present a)); intros n'; erewrite IHl; done.
    }
    assert (count_matching still_present l = count_matching still_present l') as HCMl.
    {
      specialize (HCMl' (length l)).
      rewrite firstn_all in HCMl'.
      rewrite HSameLength in HCMl'.
      by rewrite firstn_all in HCMl'.
    }
    rewrite HCMl. rewrite HCMl'.
    iMod (own_update _ _ ((● cell_list_contents_auth_ra
                               (count_matching still_present (take deqFront l'))
                               l' deqFront
                               ⋅ ◯ (ε, replicate i ε ++ [(2%nat: mnatUR, None)]))
                         ) with "HAuth") as "[HAuth #HFrag]".
    { simpl. apply auth_update_alloc.
      rewrite /cell_list_contents_auth_ra.
      destruct l as [|x l]; simpl. by inversion HIsSome.
      destruct l' as [|y l']; simpl. inversion HSameLength.
      simpl in HSameLength. rewrite HSameLength.
      clear HCMl' HCMl.
      apply prod_local_update_2.
      apply list_lookup_local_update. intros i'; destruct i'; simpl.
      - apply local_update_unital_discrete. intros z HValid.
        rewrite None_op_left_id. intros <-.
        destruct i; simpl in *.
        + inversion HIsSome; subst.
          inversion Heql'; subst. simpl. split; done.
        + rewrite -Some_op ucmra_unit_left_id.
          inversion Heql'; subst. split; done.
      - destruct i; simpl in *.
        + inversion Heql'; subst. done.
        + inversion Heql'; subst.
          revert HIsSome. clear.
          move: i i'.
          induction l; try done.
          case; simpl.
          * intros i' [=]. subst. simpl. destruct i'; simpl.
            { apply local_update_unital_discrete. intros ? _.
              rewrite None_op_left_id. intros <-. done. }
            done.
          * intros i i' ?. destruct i'; simpl.
            { apply local_update_unital_discrete. intros z HValid.
              rewrite None_op_left_id. intros <-.
              rewrite -Some_op ucmra_unit_left_id //. }
            by apply IHl.
    }
    iAssert (own γtq (◯ (ε, replicate i ε ++ [(1%nat: mnatUR, None)])))
      with "[]" as "HInit".
    {
      remember (◯ (_, _ ++ [(2%nat: mnatUR, _)])) as K.
      remember (◯ (_, _ ++ [(1%nat: mnatUR, _)])) as K'.
      assert (K' ≼ K) as HLt.
      { subst. rewrite auth_included. simpl; split; try done.
        rewrite prod_included. simpl; split; try done.
        rewrite list_lookup_included. clear.
        induction i; case; simpl; try done.
        apply Some_included; right. rewrite prod_included.
        split; try done. simpl. rewrite mnat_included. lia. }
      inversion HLt as [? ->]. rewrite own_op.
      iDestruct "HFrag" as "[$ _]". }
    iFrame.

    iMod ("HClose" with "[-]") as "$".
    2: done.

    iLeft.
    unfold cell_list_contents. iFrame.
    iSplitR; first by iPureIntro.
    iSplitR; first by iPureIntro.
    iSplitR; first by iPureIntro; lia.
    by rewrite big_sepL_later.
  }
  { (* The cell was filled already and can't be suspended to. *)

    iApply (aacc_aupd_commit with "AU"); first done.
    iIntros (l deqFront) "(>% & >HAuth & HEs & HRs & HCellRRs)".
    repeat rewrite big_sepL_later.
    iDestruct ("HIsLess" with "HAuth") as %HIsLess.
    apply lookup_lt_is_Some in HIsLess. destruct HIsLess as [cr HIsSome].

    iDestruct (big_sepL_lookup_acc with "HCellRRs")
      as "[HCellR HCellRRsRestore]".
    done.

    iAssert (▷ ⌜cr = Some (cellDone cellResumed)⌝)%I with "[-]" as "#>->".
    by iApply (enquirer_not_present_means_filled_if_initialized
                 with "HCellR [HAuth] [HCellInit] [HIsSus]"); done.

    iDestruct "HCellR"
      as (ℓ) "(>#HArrMapsto' & >HIsRes & >HCancHandle & [>HContra|[Hℓ HR]])".
    by iDestruct (iterator_issued_exclusive with "HIsSus HContra") as %[].

    iDestruct (array_mapsto_agree with "HArrMapsto HArrMapsto'") as %->.
    iAssert (▷ ℓ ↦ InjRV #0 ∧ ⌜val_is_unboxed (InjRV #0)⌝)%I with "[Hℓ]" as "HAacc".
    by iFrame.

    iAaccIntro with "HAacc".
    { iIntros "[Hℓ _] !>".
      repeat rewrite -big_sepL_later.
      iFrame. iSplitL.
      { iSplitR; first done. iApply "HCellRRsRestore".
        iFrame. iExists _. iFrame "HArrMapsto". iRight. iFrame. }
        iIntros "$". by iFrame "HCellInit". }

    iIntros "Hℓ !>". iExists RESUMEDV. iSplitL.
    2: by iIntros "$ !>"; iRight; iFrame "HCellInit".

    iRight. repeat (iSplitR; first by iPureIntro).
    repeat rewrite -big_sepL_later.
    iFrame.
    iSplitR; first by iPureIntro; lia.
    iApply "HCellRRsRestore". simpl. iExists ℓ.
    iFrame. done.
  }
Qed.

Theorem cancel_cell_spec E R γa γtq γe γd i ptr:
  rendezvous_inhabited γtq i -∗
  is_cell_pointer γa i ptr -∗
  let ap := tq_ap γtq γe in
  <<< ∀ l deqFront, ▷ is_infinite_array segment_size ap γa ∗
      ▷ cell_list_contents E R γa γtq γe γd l deqFront >>>
    cancel_cell ptr @ ⊤
  <<< is_infinite_array segment_size ap γa ∗
    cell_list_contents E R γa γtq γe γd l deqFront, RET #true >>>.
Proof.
  iIntros "#HRInh HCellPtr" (Φ) "AU". wp_lam. wp_lam.
  iDestruct "HCellPtr" as (sℓ) "[#HSegLoc ->]". wp_pures.

  wp_bind (segment_data_at _ _).

  awp_apply (segment_data_at_spec segment_size).
  { iPureIntro.
    assert (i `mod` Pos.to_nat segment_size < Pos.to_nat segment_size)%nat.
    2: lia.
    apply Nat.mod_upper_bound. lia. }
  iApply (aacc_aupd_abort with "AU"); first done.
  iIntros (? ?) "[HInfArr HCellList]".
  iDestruct (is_segment_by_location with "HSegLoc HInfArr")
    as (? ?) "[HIsSeg HArrRestore]".
  iAaccIntro with "HIsSeg".
  { iIntros "HIsSeg !>". iDestruct ("HArrRestore" with "HIsSeg") as "$".
    eauto with iFrame. }
  iIntros (dataℓ) "(HIsSeg & HArrMapsto & #HCellInv) !>".
  iDestruct (bi.later_wand with "HArrRestore HIsSeg") as "$". iFrame.
  iIntros "AU !>". wp_pures. simpl.

  wp_bind (getAndSet _ _).
  awp_apply getAndSet_spec. iApply (aacc_aupd_commit with "AU"); first done.
  iIntros (l deqFront) "[HInfArr HCellList]".
  iDestruct "HCellList" as "(>% & >HAuth & HEs & HRs & HCellResources)".

  iAssert (⌜l !! i = Some (Some cellInhabited) \/
           exists c, l !! i = Some (Some (cellDone c))⌝)%I as %HH.
  { rewrite /rendezvous_inhabited /rendezvous_state.
    iDestruct (own_valid_2 with "HAuth HRInh")
      as %[[_ HValid]%prod_included _]%auth_both_valid. simpl in *.
    iPureIntro.
    revert HValid.
    rewrite list_lookup_included.
    intros HOk. specialize (HOk i).
    assert (forall A i (x: A) v, (replicate i x ++ [v]) !! i = Some v) as HEq.
    { clear; induction i; auto. }
    rewrite HEq in HOk. revert HOk. clear. rewrite option_included.
    case; first done.
    intros (? & ? & ? & HLen & HLt).
    rewrite map_lookup in HLen.
    destruct (l !! i). 2: done.
    simpl in *. simplify_eq. destruct HLt.
    {
      left.
      destruct o; try done; simpl in *. destruct c; try done.
      all: inversion H; simpl in *; done.
    }
    {
      revert H. rewrite prod_included. simpl. case.
      rewrite mnat_included. intros H _.
      destruct o; simpl in *; try lia.
      destruct c; simpl in *; eauto; try lia.
    }
  }

  destruct HH as [HH|[cs HH]].
  {
    admit.
  }
  iDestruct (big_sepL_lookup_acc with "HCellResources") as "[HC HH]".
  by eauto.

Abort.

End proof.
