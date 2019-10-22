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
  λ: "cell'", let: "cell" := cell_ref_loc "cell'" in
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
| cellFilled
| cellAbandoned.

Notation cellProgressUR := mnatUR (only parsing).
Notation cellUninitializedO := (0%nat: mnatUR) (only parsing).
Notation cellInitializedO := (1%nat: mnatUR) (only parsing).
Notation cellInhabitedO := (2%nat: mnatUR) (only parsing).
Notation cellDoneO := (3%nat: mnatUR) (only parsing).

Canonical Structure cellTerminalStateO := leibnizO cellTerminalState.

Notation cellStateUR := (prodUR (prodUR (optionUR (exclR unitO)) cellProgressUR)
                                (optionUR (agreeR cellTerminalStateO))).

Notation queueContentsUR := (listUR cellStateUR).

Notation enqueueUR := natUR.
Notation dequeueUR := (prodUR natUR mnatUR).
Notation algebra := (authUR (prodUR (prodUR enqueueUR dequeueUR) queueContentsUR)).

Class threadQueueG Σ := ThreadQueueG { thread_queue_inG :> inG Σ algebra }.
Definition threadQueueΣ : gFunctors := #[GFunctor algebra].
Instance subG_threadQueueΣ {Σ} : subG threadQueueΣ Σ -> threadQueueG Σ.
Proof. solve_inG. Qed.

Context `{heapG Σ} `{iArrayG Σ} `{iteratorG Σ} `{threadQueueG Σ} (N: namespace).
Notation iProp := (iProp Σ).

Variable segment_size: positive.

Definition rendezvous_state γtq i (r: cellStateUR) :=
  own γtq (◯ (ε, {[ i := r ]})).

Global Instance rendezvous_state_persistent γtq i (r: cellStateUR):
  CoreId r -> Persistent (rendezvous_state γtq i r).
Proof. apply _. Qed.

Definition rendezvous_done γtq i (c: cellTerminalState) :=
  rendezvous_state γtq i ((ε, cellDoneO), Some (to_agree c)).

Definition rendezvous_resumed (γtq: gname) (i: nat): iProp :=
  rendezvous_done γtq i cellResumed.
Definition rendezvous_filled (γtq: gname) (i: nat): iProp :=
  rendezvous_done γtq i cellFilled.
Definition rendezvous_cancelled (γtq: gname) (i: nat): iProp :=
  rendezvous_done γtq i cellCancelled.
Definition rendezvous_abandoned (γtq: gname) (i: nat): iProp :=
  rendezvous_done γtq i cellAbandoned.
Definition rendezvous_initialized γtq i :=
  rendezvous_state γtq i (ε, cellInitializedO, ε).
Definition rendezvous_inhabited γtq i :=
  rendezvous_state γtq i (ε, cellInhabitedO, ε).

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
  move: n Z Hel pv. clear. induction l.
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
    | None => (None, cellUninitializedO, None)
    | Some s => match s with
               | cellInhabited => (Excl' (), cellInhabitedO, None)
               | cellDone d => (match d with
                               | cellCancelled => None
                               (* Must give up the token to cancel the cell *)
                               | cellFilled => None
                               (* The cell is never inhabited *)
                               | _ => Excl' ()
                               end, cellDoneO, Some (to_agree d))
               end
  end.

Definition inhabitant_token γtq i :=
  rendezvous_state γtq i (Excl' (), ε, ε).

Lemma inhabitant_token_exclusive γtq i:
  inhabitant_token γtq i -∗ inhabitant_token γtq i -∗ False.
Proof.
  iIntros "H H'".
  iDestruct (own_valid_2 with "H H'") as %HValid.
  iPureIntro. move: HValid.
  rewrite -auth_frag_op auth_frag_valid -pair_op pair_valid.
  case; intros _.
  rewrite list_lookup_valid. intros HValid.
  specialize (HValid i). move: HValid.
  rewrite list_lookup_op.

  rewrite lookup_app_r. all: rewrite replicate_length. 2: done.
  rewrite minus_diag. simpl.

  rewrite -Some_op -pair_op Some_valid pair_valid. case.
  intros HH _. revert HH. rewrite -pair_op pair_valid. case.
  intros HH _. revert HH. rewrite -Some_op Some_valid.
  apply exclusive_l. apply excl_exclusive.
Qed.

Definition deq_front_at_least γtq (n: nat) :=
  own γtq (◯ (ε, (ε, n: mnatUR), ε)).

Definition cell_resources E R γtq γa γe γd i k :=
  (match k with
   | None => True
   | Some cellState => ∃ ℓ, array_mapsto segment_size γa i ℓ ∗
        match cellState with
        | cellInhabited => (∃ (th: loc), ℓ ↦ InjLV #th)
                            ∗ iterator_issued γe i
                            ∗ cell_cancellation_handle segment_size γa i
        | cellDone cd => match cd with
          | cellAbandoned => cell_cancellation_handle segment_size γa i ∗
                            iterator_issued γe i ∗
                            inhabitant_token γtq i ∗
                            deq_front_at_least γtq (S i) ∗
                            (iterator_issued γd i ∨ (∃ (th: loc), ℓ ↦ InjLV #th) ∗ E)
          | cellCancelled => iterator_issued γe i ∗ (ℓ ↦ CANCELLEDV ∨ ℓ ↦ RESUMEDV)
          | cellFilled => iterator_issued γd i ∗
                          cell_cancellation_handle segment_size γa i ∗
                          (iterator_issued γe i ∨ ℓ ↦ RESUMEDV ∗ R)
          | cellResumed => iterator_issued γd i ∗
                          cell_cancellation_handle segment_size γa i ∗
                          iterator_issued γe i ∗
                           (inhabitant_token γtq i ∨ ℓ ↦ RESUMEDV ∗ R)
          end
        end
  end)%I.

Theorem cell_resources_timeless S R γtq γa γe γd i k :
  Timeless R -> Timeless S ->
  Timeless (cell_resources S R γtq γa γe γd i k).
Proof. destruct k; try apply _. destruct c; try apply _.
       destruct c; apply _.
Qed.

Definition option_Pos_of_nat (n: nat): option positive :=
  match n with
  | O => None
  | S n' => Some (Pos.of_nat n)
  end.

Definition cell_list_contents_auth_ra l (deqFront: nat) :=
  (length l, ((deqFront + count_matching (fun b => not (still_present b)) (drop deqFront l))%nat,
              deqFront: mnatUR), map cell_state_to_RA l).

Definition cell_list_contents (S R: iProp) γa γtq γe γd
           (l: list (option cellState)) (deqFront: nat): iProp :=
  (let nEnq := count_matching still_present l in
   let nDeq := count_matching still_present (take deqFront l) in
   ⌜deqFront <= length l⌝ ∗
   ([∗ list] x ∈ drop deqFront l, ⌜x = Some (cellDone cellCancelled) ∨
                                   x = Some cellInhabited ∨
                                   x = None⌝) ∗
   own γtq (● cell_list_contents_auth_ra l deqFront) ∗
       ([∗ list] s ∈ replicate nEnq S, s) ∗ ([∗ list] r ∈ replicate nDeq R, r) ∗
       ([∗ list] i ↦ k ∈ l, cell_resources S R γtq γa γe γd i k))%I.

Definition suspension_permit γtq := own γtq (◯ (1%nat, ε, ε)).

Definition exists_list_element γtq (n: nat) :=
  own γtq (◯ (ε, replicate n ε ++ [ε])).

Theorem exists_list_element_lookup γtq l i d:
  exists_list_element γtq i -∗
  own γtq (● (cell_list_contents_auth_ra l d)) -∗
  ⌜exists v, l !! i = Some v⌝.
Proof.
  iIntros "HExistsEl HAuth".
  iDestruct (own_valid_2 with "HAuth HExistsEl")
    as %[[_ HH]%prod_included _]%auth_both_valid.
  simpl in *. iPureIntro.
  revert HH. rewrite list_lookup_included=> HH.
  specialize (HH i). move: HH. rewrite option_included.
  case. intros HH; exfalso; by induction i.
  intros (a & b & _ & HH & _). move: HH.
  rewrite map_lookup. destruct (l !! i); simpl; first by eauto.
  done.
Qed.

Lemma cell_list_contents_append E R γa γtq γe γd l deqFront:
  E -∗ cell_list_contents E R γa γtq γe γd l deqFront ==∗
  (suspension_permit γtq ∗
  exists_list_element γtq (length l)) ∗
  cell_list_contents E R γa γtq γe γd (l ++ [None]) deqFront.
Proof.
  rewrite /suspension_permit -own_op -auth_frag_op
    -pair_op ucmra_unit_left_id ucmra_unit_right_id.
  iIntros "HS (% & #HNotCanc & HAuth & HSs & HRs & HCellResources)".
  iMod (own_update with "HAuth") as "[HAuth HFrag]".
  2: {
    iFrame "HFrag". iSplitR.
    { iPureIntro. rewrite app_length. lia. }
    replace (take deqFront (l ++ [None])) with (take deqFront l).
    2: by rewrite take_app_le; [done|lia].

    iFrame "HAuth".
    rewrite count_matching_app replicate_plus big_sepL_app /=; iFrame.
    rewrite drop_app_le. 2: lia.
    rewrite big_sepL_app.
    simpl. iFrame "HNotCanc". iSplitL. 2: done. by eauto.
  }
  apply auth_update_alloc.
  apply prod_local_update'.
  rewrite app_length; simpl.
  apply prod_local_update; simpl; first by apply nat_local_update.
  rewrite drop_app_le.
    by rewrite count_matching_app /= -plus_n_O.
    by lia.

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

Definition awakening_permit γtq := own γtq (◯ (ε, (1%nat, ε), ε)).

Instance deq_front_at_least_persistent γtq n:
  Persistent (deq_front_at_least γtq n).
Proof.
  apply own_core_persistent, auth_frag_core_id, pair_core_id; apply _.
Qed.

Theorem deq_front_at_least__cell_list_contents γtq n l deqFront :
  deq_front_at_least γtq n -∗
  own γtq (● cell_list_contents_auth_ra l deqFront) -∗
  ⌜n <= deqFront⌝.
Proof.
  iIntros "H1 H2".
  iDestruct (own_valid_2 with "H2 H1") as
      %[[[_ [_ HValid%mnat_included]%prod_included]%prod_included
                                                   _]%prod_included
                                                     _]%auth_both_valid.
  iPureIntro; simpl in *; lia.
Qed.

Theorem count_matching_le_length
        {A} (P: A -> Prop) {H': forall x, Decision (P x)} (l: list A):
  (count_matching P l <= length l)%nat.
Proof. induction l; first done. simpl. destruct (decide (P a)); lia. Qed.

Theorem count_matching_complement
        {A} (P: A -> Prop) {H': forall x, Decision (P x)} (l: list A):
  count_matching (fun b => not (P b)) l = (length l - count_matching P l)%nat.
Proof.
  induction l; first done.
  simpl.
  destruct (decide (P a)); destruct (decide (not (P a))); try contradiction.
  done.
  rewrite -minus_Sn_m. auto.
  apply count_matching_le_length.
Qed.

Theorem count_matching_take
        {A} (P: A -> Prop) {H': forall x, Decision (P x)} (l: list A):
  forall i, count_matching P (take i l) =
       (count_matching P l - count_matching P (drop i l))%nat.
Proof.
  intros i.
  replace (count_matching P l) with (count_matching P (take i l ++ drop i l)).
  2: by rewrite take_drop.
  rewrite count_matching_app. lia.
Qed.

Theorem count_matching_drop
        {A} (P: A -> Prop) {H': forall x, Decision (P x)} (l: list A):
  forall i, count_matching P (drop i l) =
       (count_matching P l - count_matching P (take i l))%nat.
Proof.
  intros i.
  replace (count_matching P l) with (count_matching P (take i l ++ drop i l)).
  2: by rewrite take_drop.
  rewrite count_matching_app. lia.
Qed.

Lemma cell_list_contents_register_for_dequeue E R γa γtq γe γd l deqFront:
  forall i, find_index still_present (drop deqFront l) = Some i ->
  R -∗ cell_list_contents E R γa γtq γe γd l deqFront ==∗
  (awakening_permit γtq ∗ deq_front_at_least γtq (deqFront + S i)%nat) ∗
  cell_list_contents E R γa γtq γe γd l (deqFront + S i)%nat.
Proof.
  rewrite /awakening_permit /deq_front_at_least.
  iIntros (i HFindSome) "HR (% & #HNotDone & HAuth & HSs & HRs & HCellResources)".
  rewrite -own_op -auth_frag_op.
  repeat rewrite -pair_op ucmra_unit_left_id. rewrite ucmra_unit_right_id.

  apply find_index_Some in HFindSome.
  destruct HFindSome as [[v [HIn HPresent]] HNotPresent].
  assert (i < length (drop deqFront l))%nat as HLt.
  { apply lookup_lt_is_Some. by eexists. }

  assert (count_matching still_present (take i (drop deqFront l)) = O)
    as HCountMatching2.
  {
    remember (drop deqFront l) as l'.
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

  assert (count_matching still_present (take 1 (drop (deqFront + i) l)) = 1%nat)
    as HCountMatching3.
  {
    replace (drop (deqFront + i) l) with (v :: drop (deqFront + S i) l).
    { simpl. by rewrite decide_left. }
    rewrite lookup_drop in HIn.
    assert (deqFront + i = length (take (deqFront + i) l))%nat as HH.
    {
      rewrite take_length_le. done.
      assert (deqFront + i < length l)%nat as HLt'. 2: lia.
      apply lookup_lt_is_Some_1. by eauto.
    }
    replace (drop (deqFront + i) l) with
        (drop (deqFront + i) (take (deqFront + i) l ++ v :: drop (deqFront + S i) l)).
    { symmetry. rewrite drop_app_le. rewrite drop_ge. done. all: lia. }
    by rewrite -plus_n_Sm take_drop_middle.
  }

  assert (take i (drop deqFront l) ++ take 1 (drop (deqFront + i) l) =
          take (S i) (drop deqFront l)) as HTakeApp.
  {
    replace (take (S i) (drop deqFront l)) with
        (take (i + 1)%nat (take i (drop deqFront l) ++ drop (deqFront + i) l)).
    rewrite take_plus_app; first done.
    rewrite take_length_le; first done.
    lia.
    rewrite Nat.add_comm. simpl. congr (take (S i)).
    replace (drop (deqFront + i) l) with (drop i (drop deqFront l)).
    by rewrite take_drop.
    by rewrite drop_drop.
  }

  assert (S (count_matching still_present (take deqFront l)) =
              count_matching still_present (take (deqFront + S i) l)) as HCountMatching.
  {
    replace (take (deqFront + S i) l) with
        (take (deqFront + S i) (take deqFront l ++ drop deqFront l)).
    2: by rewrite take_drop.
    rewrite take_plus_app. 2: rewrite take_length_le; lia.
    rewrite count_matching_app.
    replace (take (S i) (drop deqFront l)) with
        (take i (drop deqFront l) ++ take 1 (drop (deqFront + i) l)).
    rewrite count_matching_app HCountMatching2 HCountMatching3; lia.
  }

  iMod (own_update with "HAuth") as "[HAuth HFrag]".
  2: {
    iFrame "HFrag". iSplitR.
    { iPureIntro. rewrite drop_length in HLt. lia. }
    iFrame. rewrite -HCountMatching. simpl. iFrame.
    repeat rewrite big_sepL_forall.
    iIntros "!>" (k ? HEv). iApply ("HNotDone" $! (k + S i)%nat).
    iPureIntro. rewrite <- HEv.
    repeat rewrite lookup_drop. congr (fun x => l !! x). lia.
  }

  apply auth_update_alloc, prod_local_update_1, prod_local_update_2,
    prod_local_update'.
  2: apply mnat_local_update; lia.
  apply nat_local_update.
  repeat rewrite count_matching_complement drop_length.
  repeat rewrite -Nat.add_assoc. congr (Nat.add deqFront).
  rewrite Nat.add_comm. simpl. congr S. rewrite /ε /nat_unit -plus_n_O.
  rewrite Nat.sub_add_distr.
  rewrite -drop_drop.

  replace (count_matching still_present (drop deqFront l)) with
      (count_matching still_present (take (S i) (drop deqFront l) ++
                                          drop (S i) (drop deqFront l))).
  2: by rewrite take_drop.

  rewrite -HTakeApp.
  repeat rewrite count_matching_app.
  repeat rewrite HCountMatching2.
  rewrite HCountMatching3. simpl.

  remember (count_matching (_) (drop (S i) _)) as K.
  assert (K <= length l - deqFront - S i)%nat as HKLt.
  {
    rewrite HeqK. eapply transitivity.
    apply count_matching_le_length. rewrite drop_drop.
    rewrite drop_length.
    lia.
  }
  assert (deqFront + i < length l)%nat as HDILt.
  {
    apply lookup_lt_is_Some.
    rewrite lookup_drop in HIn.
    eauto.
  }
  lia.

Qed.

Definition is_thread_queue (S R: iProp) γa γtq γe γd eℓ epℓ dℓ dpℓ l deqFront :=
  let ap := tq_ap γtq γe in
  (is_infinite_array segment_size ap γa ∗
   cell_list_contents S R γa γtq γe γd l deqFront ∗
   ([∗ list] i ↦ b ∈ l, match b with
                        | Some (cellDone cellCancelled) =>
                          awakening_permit γtq ∨ iterator_issued γd i
                        | _ => True
                        end) ∗
   ∃ (enqIdx deqIdx: nat),
   iterator_points_to segment_size γa γe eℓ epℓ enqIdx ∗
   iterator_points_to segment_size γa γd dℓ dpℓ deqIdx ∗
   ([∗ list] i ∈ seq 0 deqIdx, awakening_permit γtq) ∗
   ⌜deqIdx <= deqFront <= length l⌝ ∧ ⌜enqIdx <= length l⌝
  )%I.

Lemma pair_op_1 {A: ucmraT} {B: cmraT} (b b': B):
  (b ⋅ b', ε) ≡ (b, (ε: A)) ⋅ (b', (ε: A)).
Proof. by rewrite -pair_op ucmra_unit_left_id. Qed.

Lemma awakening_permit_implies_bound i (E R: iProp) γtq γa γd γe dℓ l deqFront deqIdx:
  ⌜(deqIdx <= deqFront)%nat⌝ -∗
  ([∗ list] i ∈ seq 0 i, awakening_permit γtq) -∗
  iterator_counter γd dℓ deqIdx -∗
   ([∗ list] i ∈ seq 0 deqIdx, awakening_permit γtq) -∗
  cell_list_contents E R γa γtq γe γd l deqFront -∗
   ([∗ list] i ↦ b ∈ l, match b with
                        | Some (cellDone cellCancelled) =>
                          awakening_permit γtq ∨ iterator_issued γd i
                        | _ => True
                        end) -∗
   ⌜deqIdx + i <= deqFront⌝.
Proof.
  iIntros (HLt) "HCAwaks HCounter HDeqAwaks HCellResources HCancAwaks".
  iDestruct "HCellResources" as "(% & #HNotDone & HAuth & _ & _ & HRRs)".
  replace l with (take deqFront l ++ drop deqFront l).
  2: by rewrite take_drop.
  repeat rewrite big_sepL_app.
  iDestruct "HRRs" as "[_ HRRs]".
  iDestruct "HCancAwaks" as "[_ HCancAwaks]".
  rewrite /iterator_counter. iDestruct "HCounter" as "[_ HCtrAuth]".
  rewrite take_length_le. 2: lia.

  rewrite drop_app_ge take_length_le; try lia. rewrite minus_diag drop_0.

  assert (forall k, own γd (● (GSet (set_seq 0 deqIdx), deqIdx: mnatUR)) -∗
                      iterator_issued γd (deqIdx + k) -∗ False)%I as HContra.
  {
    iIntros (k) "HCtrAuth HIsSus".
    iDestruct (own_valid_2 with "HCtrAuth HIsSus") as
        %[[_ HValid%mnat_included]%prod_included _]%auth_both_valid.
    simpl in *. lia.
  }
  iAssert (⌜forall j, (deqFront <= j < length l)%nat ->
                l !! j = Some None \/
                l !! j = Some (Some cellInhabited) \/
                l !! j = Some (Some (cellDone cellCancelled))⌝)%I with "[-]" as %HH.
  {
    rewrite big_sepL_forall. iIntros (j [HB1 HB2]).
    apply lookup_lt_is_Some_2 in HB2. destruct HB2 as [v HB2].
    iSpecialize ("HNotDone" $! (j-deqFront)%nat v).
    rewrite lookup_drop. replace (deqFront + (_ - _))%nat with j by lia.
    iDestruct ("HNotDone" with "[]") as "HH"; first done.
    rewrite HB2.
    iDestruct "HH" as "[->|[->|->]]"; eauto.
  }
  iAssert ([∗ list] k ↦ y ∈ drop deqFront l, if (decide (not (still_present y)))
                                             then
                                               awakening_permit γtq ∨
                                               (∃ k', iterator_issued γd (deqFront + k'))
                                             else True)%I
    with "[HCancAwaks]" as "HAwak".
  {
    iDestruct (big_sepL_mono with "HCancAwaks") as "$".
    iIntros (k v HEv) "HV".
    rewrite lookup_drop in HEv.
    destruct (HH (deqFront + k)%nat) as [HE|[HE|HE]]; simplify_eq; simpl in *;
      eauto.
    { split; try lia. apply lookup_lt_is_Some. by eauto. }
    iDestruct "HV" as "[V|V]"; by eauto.
  }
  clear HH.
  iAssert ([∗ list] y ∈ drop deqFront l,
           if decide (not (still_present y)) then awakening_permit γtq
           else True)%I with "[HCtrAuth HAwak]" as "HAwak".
  {
    remember (drop deqFront l) as l'.
    assert (exists n, deqFront = deqIdx + n)%nat as HH.
    { rewrite -nat_le_sum. lia. }
    destruct HH as [v ->].
    revert HContra. clear.
    move=> HContra.
    iClear "HNotDone".
    iInduction l' as [|x l'] "IH"; simpl.
    done.
    destruct (decide (not (still_present x))).
    {
      iDestruct "HAwak" as "[[$|HContra] HIx]".
      by iApply ("IH" with "HCtrAuth HIx").

      iDestruct "HContra" as (?) "HIsSus".
      iExFalso.
      iApply (HContra with "HCtrAuth").
      by rewrite -Nat.add_assoc.
    }
    {
      iDestruct "HAwak" as "[_ HInd]".
      iSplitR; first done.
      by iApply ("IH" with "HCtrAuth").
    }
  }
  iAssert (∀ s, [∗ list] _ ∈ seq s (count_matching
                                          (fun k => not (still_present k))
                                          (drop deqFront l)),
           awakening_permit γtq)%I with "[HAwak]" as "HAwak".
  {
    iClear "HNotDone".
    iInduction (drop deqFront l) as [|x l'] "IH"; simpl.
    done.
    destruct (decide (not (still_present x))); simpl.
    1: iDestruct "HAwak" as "[$ HI]".
    2: iDestruct "HAwak" as "[_ HI]".
    all: iIntros (v); by iApply ("IH" with "HI").
  }
  iSpecialize ("HAwak" $! O).
  iCombine "HCAwaks" "HDeqAwaks" as "HAwaks".
  iCombine "HAwaks" "HAwak" as "HAwaks".
  repeat rewrite -big_sepL_app.
  rewrite big_opL_irrelevant_element'.
  repeat rewrite app_length.
  repeat rewrite seq_length.

  rewrite /awakening_permit.

  destruct i.
  iPureIntro. lia.

  remember ((_ + _) + _)%nat as A.
  assert (0 < A)%nat as HNZ by lia.

  iAssert (own γtq (◯ (ε, (A, ε), ε))) with "[HAwaks]" as "HAwak".
  {
    change (seq O A) with (seq (O + O)%nat A).
    remember (O + O)%nat as s. move: HNZ. clear. intros HNZ.
    iInduction A as [|A] "IH" forall (s).
    lia.
    simpl.
    inversion HNZ; subst; simpl.
    by iDestruct "HAwaks" as "[$ _]".
    change (S A) with (1%nat ⋅ A).
    rewrite pair_op_1 pair_op_2 pair_op_1 auth_frag_op own_op.
    iDestruct "HAwaks" as "[$ HIH]".
    iApply "IH".
    by iPureIntro; lia.
    done.
  }

  rewrite take_drop.

  iDestruct (own_valid_2 with "HAuth HAwak") as
      %[[[_ [HValid%nat_included
                   _]%prod_included]%prod_included
                                    _]%prod_included _]%auth_both_valid.
  simpl in *.
  subst.
  iPureIntro.
  lia.

Qed.

Definition is_cell_pointer' γa (ix ic: nat) (v: val) :=
  (∃ (ℓ: loc), segment_location γa ix ℓ ∗ ⌜v = (#ℓ, #ic)%V⌝)%I.

Definition is_cell_pointer γa i v :=
  ias_cell_info_view segment_size (fun ix ic => is_cell_pointer' γa ix ic v) i.

Theorem is_cell_pointer'_persistent γa ix ic v:
  Persistent (is_cell_pointer' γa ix ic v).
Proof. apply _. Qed.

Lemma cell_list_contents_lookup_acc i E R γa γtq γe γd l deqFront:
  cell_list_contents E R γa γtq γe γd l deqFront -∗
  cell_resources E R γtq γa γe γd i (mjoin (l !! i)) ∗
  (cell_resources E R γtq γa γe γd i (mjoin (l !! i)) -∗
   cell_list_contents E R γa γtq γe γd l deqFront).
Proof.
  iIntros "(% & #HNotDone & HAuth & HEs & HRs & HCellResources)".
  iFrame "HNotDone".
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

Lemma big_sepL_lookup_alter_abort {A: Type} i s f (P: nat -> A -> iProp) (l: list A) v:
  l !! i = Some v ->
  ([∗ list] i ↦ k ∈ l, P (s+i)%nat k) -∗
  (P (s+i)%nat v ∗ ((P (s+i)%nat v -∗ [∗ list] i ↦ k ∈ l, P (s+i)%nat k) ∧
                    (P (s+i)%nat (f v) -∗
                       [∗ list] i ↦ k ∈ (alter f i l), P (s+i)%nat k))).
Proof.
  iIntros (HEl) "HList".
  iInduction l as [|x l'] "IH" forall (s i HEl); first by inversion HEl.
  destruct i; simpl in *.
  - inversion HEl; subst.
    rewrite Nat.add_0_r. iDestruct "HList" as "[$ $]".
    iSplit; by iIntros "$".
  - iDestruct "HList" as "[$ HList]".
    rewrite -plus_n_Sm.
    iDestruct ("IH" $! (S s) i HEl with "[HList]") as "[$ HLst] /=".
    { iDestruct (big_sepL_mono with "HList") as "$".
      iIntros (? ? ?) "HAp". by rewrite -plus_n_Sm. }
    iSplit; iIntros "HPs".
    1: iDestruct "HLst" as "[HLst _]".
    2: iDestruct "HLst" as "[_ HLst]".
    all: iDestruct ("HLst" with "HPs") as "HLst".
    all: iDestruct (big_sepL_mono with "HLst") as "$".
    all: iIntros (? ? ?) "HAp". all: by rewrite -plus_n_Sm.
Qed.

Lemma cell_resources_conflict_invariant E R γtq γa γe γd i c ptr:
  cell_resources E R γtq γa γe γd i (Some c) -∗
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
    * iDestruct "HR" as "(_ & HCancHandle' & _)".
      iApply (cell_cancellation_handle'_exclusive with "HCancHandle HCancHandle'").
    * iDestruct "HR" as "(HCancHandle' & _)".
      iApply (cell_cancellation_handle'_exclusive with "HCancHandle HCancHandle'").
Qed.

Lemma enquirer_not_present_means_filled_if_initialized
      E R γtq γa γe γd i c l d:
  l !! i = Some c ->
  cell_resources E R γtq γa γe γd i c -∗
  own γtq (● cell_list_contents_auth_ra l d) -∗
  rendezvous_initialized γtq i -∗
  iterator_issued γe i -∗
  ⌜c = Some (cellDone cellFilled)⌝.
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
    intros HH. simplify_eq. simpl.
    rewrite /= Some_included prod_included /=. case.
    by repeat case.
    case. rewrite prod_included. simpl. case.
    rewrite mnat_included; lia.
  }
  destruct c; simpl.
  {
    iDestruct "HCellRes" as (?) "(_ & _ & HIsSus' & _)".
    iDestruct (iterator_issued_exclusive with "HIsSus HIsSus'") as %[].
  }
  destruct c; simpl; auto; iExFalso.
  1: iDestruct "HCellRes" as (?) "(_ & HIsSus' & _)".
  2: iDestruct "HCellRes" as (?) "(_ & _ & _ & HIsSus' & _)".
  3: iDestruct "HCellRes" as (?) "(_ & _ & HIsSus' & _)".
  all: iDestruct (iterator_issued_exclusive with "HIsSus HIsSus'") as %[].
Qed.

Lemma None_op_left_id {A: cmraT} (a: option A): None ⋅ a = a.
Proof. rewrite /op /cmra_op /=. by destruct a. Qed.

Theorem inhabit_cell_spec N' E R γa γtq γe γd i ptr (th: loc):
  iterator_issued γe i -∗
  exists_list_element γtq i -∗
  array_mapsto segment_size γa i ptr -∗
  inv N' (cell_invariant γtq γa i ptr) -∗
  <<< ∀ l deqFront, ▷ cell_list_contents E R γa γtq γe γd l deqFront >>>
    getAndSet #ptr (InjLV #th) @ ⊤ ∖ ↑N'
  <<< ∃ r, ⌜l !! i = Some None⌝ ∧
           ⌜r = InjLV #()⌝ ∧
           inhabitant_token γtq i ∗
           ▷ cell_list_contents E R γa γtq γe γd
             (alter (fun _ => Some cellInhabited) i l) deqFront ∨
           ⌜l !! i = Some (Some (cellDone cellFilled))⌝ ∧
           ⌜r = RESUMEDV⌝ ∧
           ▷ R ∗
           ▷ cell_list_contents E R γa γtq γe γd l deqFront , RET r >>>.
Proof.
  iIntros "HIsSus #HExistsEl #HArrMapsto #HCellInv" (Φ) "AU".
  awp_apply getAndSet_spec.

  iInv N' as "[[>HCancHandle >Hℓ]|>#HCellInit]".
  { (* The cell wasn't in the list, so the resumer has not yet arrived. *)
    iAssert (▷ ptr ↦ InjLV #() ∧ ⌜val_is_unboxed (InjLV #())⌝)%I with "[Hℓ]" as "HAacc".
    by iFrame.

    iAaccIntro with "HAacc".
    { iFrame. unfold cell_invariant. iIntros "[? _]".
      iLeft. iFrame. done. }
    iIntros "Hℓ".

    iMod "AU" as (l deqFront) "[(>HLt & >#HNotDone & >HAuth & HEs & HRs & HCellRRs) [_ HClose]]".
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
                               l' deqFront
                               ⋅ ◯ (ε, replicate i ε ++
                                                 [(Excl' (), 2%nat: mnatUR, None)]))
                         ) with "HAuth") as "[HAuth HFrag]".
    { simpl. apply auth_update_alloc.
      rewrite /cell_list_contents_auth_ra.
      assert (count_matching (fun b => not (still_present b)) (drop deqFront l) =
              count_matching (fun b => not (still_present b)) (drop deqFront l')) as ->.
      {
        subst. revert HIsSome. clear. revert i. revert deqFront.
        induction l; intros; first by inversion HIsSome.
        destruct i; simpl.
        { inversion HIsSome; subst. by destruct deqFront. }
        destruct deqFront; simpl in *.
        { specialize (IHl O i). unfold drop in IHl. by rewrite IHl. }
        erewrite IHl. 2: done. done.
      }

      rewrite HSameLength.
      apply prod_local_update_2. clear HCMl' HCMl HSameLength.
      apply list_lookup_local_update. subst. revert i HIsSome.
      induction l; first done; intros i HIsSome i'.
      destruct i; simpl in *.
      { simplify_eq. destruct i'; try done. simpl in *. clear.
        apply local_update_unital_discrete. intros z. rewrite None_op_left_id.
        intros _ <-. done. }
      destruct i'; simpl.
      { apply local_update_unital_discrete. intros z. rewrite None_op_left_id.
        intros HValid <-. split; first done.
        by rewrite -Some_op ucmra_unit_left_id. }
      by apply IHl.
    }
    iAssert (own γtq (◯ (ε, replicate i ε ++ [(ε, 1%nat: mnatUR, None)])))
      with "[-]" as "#HInit".
    {
      remember (◯ (_, _ ++ [(_, 2%nat: mnatUR, _)])) as K.
      remember (◯ (_, _ ++ [(_, 1%nat: mnatUR, _)])) as K'.
      assert (K' ≼ K) as HLt.
      { subst. rewrite auth_included. simpl; split; try done.
        rewrite prod_included. simpl; split; try done.
        rewrite list_lookup_included. clear.
        induction i; case; simpl; try done.
        apply Some_included; right. rewrite prod_included.
        split; try done. simpl. rewrite prod_included. simpl. split.
        apply ucmra_unit_least. rewrite mnat_included. lia. }
      inversion HLt as [? ->]. rewrite own_op.
      iDestruct "HFrag" as "[$ _]". }
    iFrame.

    iMod ("HClose" with "[-]") as "$".
    2: by iFrame "HInit".

    iLeft.
    unfold cell_list_contents. iFrame.
    iSplitR; first by iPureIntro.
    iSplitR; first by iPureIntro.
    iSplitL "HFrag". {
      rewrite /inhabitant_token /rendezvous_state.
      iApply own_mono. 2: iApply "HFrag".
      apply auth_included. split; try done. simpl.
      apply prod_included. split; try done. simpl.
      apply list_lookup_included. clear.
      induction i; case; simpl; try done.
      { apply Some_included. right. apply prod_included; split; try done; simpl.
        rewrite prod_included. split; try done; simpl.
        apply ucmra_unit_least. }
    }
    rewrite HSameLength.
    iSplitL "HLt"; first done.
    iSplitR.
    2: by rewrite big_sepL_later.
    repeat rewrite big_sepL_forall.
    iIntros (k x).
    destruct (decide (i = (deqFront + k)%nat)).
    {
      subst i l'. rewrite lookup_drop list_lookup_alter.
      destruct (l !! (deqFront + k)%nat); simpl.
      2: done.
      iIntros (HH). simplify_eq. eauto.
    }
    iSpecialize ("HNotDone" $! k x). repeat rewrite lookup_drop.
    subst l'. rewrite list_lookup_alter_ne. 2: lia.
    iIntros (HH). iApply "HNotDone". by iPureIntro.
  }
  { (* The cell was filled already and can't be suspended to. *)

    iApply (aacc_aupd_commit with "AU"); first done.
    iIntros (l deqFront) "(>% & >#HNotDone & >HAuth & HEs & HRs & HCellRRs)".
    repeat rewrite big_sepL_later.
    iDestruct (exists_list_element_lookup with "HExistsEl HAuth") as %[cr HIsSome].
    iDestruct (big_sepL_lookup_acc with "HCellRRs")
      as "[HCellR HCellRRsRestore]".
    done.

    iAssert (▷ ⌜cr = Some (cellDone cellFilled)⌝)%I with "[-]" as "#>->".
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
      { iSplitR; first done. iFrame "HNotDone".
        iApply "HCellRRsRestore".
        iFrame. iExists _. iFrame "HArrMapsto". iRight. iFrame. }
        iIntros "$". by iFrame "HCellInit". }

    iIntros "Hℓ !>". iExists RESUMEDV. iSplitL.
    2: by iIntros "$ !>"; iRight; iFrame "HCellInit".

    iRight. repeat (iSplitR; first by iPureIntro).
    repeat rewrite -big_sepL_later.
    iFrame.
    iSplitR; first by iPureIntro; lia. iFrame "HNotDone".
    iApply "HCellRRsRestore". simpl. iExists ℓ.
    iFrame. done.
  }
Qed.

Lemma inhabited_cell_states γtq i l deqFront:
  own γtq (● cell_list_contents_auth_ra l deqFront) -∗
  inhabitant_token γtq i -∗
  ⌜l !! i = Some (Some cellInhabited)⌝ ∨
  ⌜l !! i = Some (Some (cellDone cellResumed))⌝ ∨
  ⌜l !! i = Some (Some (cellDone cellAbandoned))⌝.
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
  rewrite minus_diag /= option_included. case; first done.
  intros (a & b & ? & HContent & HH). simplify_eq.
  destruct (l !! i) as [o|]; simpl in *.
  2: done.
  simplify_eq.
  revert HH. repeat rewrite prod_included /=.
  rewrite option_included.
  destruct o as [c|]; simpl in *.
  destruct c as [|cd]; first by eauto.
  destruct cd; eauto.
  all: case; first by case; case; intros HH; inversion HH.
  all: case; case; case; try done; by intros (? & ? & ? & HH & _).
Qed.

Lemma drop_alter' {A} (f: A -> A) n i (l: list A):
  drop n (alter f (n+i)%nat l) = alter f i (drop n l).
Proof.
  revert n.
  induction l; first by case.
  case; first done.
  auto.
Qed.

Theorem cancel_rendezvous_spec E R γa γtq γe γd i ℓ:
  array_mapsto segment_size γa i ℓ -∗
  inhabitant_token γtq i -∗
  let ap := tq_ap γtq γe in
  <<< ∀ l deqFront, ▷ cell_list_contents E R γa γtq γe γd l deqFront >>>
    getAndSet #ℓ CANCELLEDV = RESUMEDV @ ⊤
  <<< ∃ v, (⌜l !! i = Some (Some (cellDone cellResumed))⌝ ∧
     ⌜v = #true⌝ ∧
     ▷ cell_list_contents E R γa γtq γe γd l deqFront ∗ ▷ R ∨
     ⌜l !! i = Some (Some cellInhabited)⌝ ∧
     ⌜v = #false⌝ ∧
     cell_cancellation_handle segment_size γa i ∗ ▷ E ∗
     (⌜i < deqFront⌝ ∧ ▷ R ∨ ⌜i >= deqFront⌝ ∧ awakening_permit γtq) ∗
     rendezvous_cancelled γtq i ∗
     ▷ cell_list_contents E R γa γtq γe γd
      (alter (fun _ => Some (cellDone cellCancelled)) i l) deqFront)
  , RET v >>>.
Proof.
  (*
  iIntros "HInhToken HCellPtr" (Φ) "AU". wp_lam. wp_lam.
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
*)
  iIntros "#HArrMapsto HInhToken" (Φ) "AU".

  awp_apply getAndSet_spec. iApply (aacc_aupd_commit with "AU"); first done.
  iIntros (l deqFront) "(>% & >#HNotDone & >HAuth & HEs & HRs & HCellResources)".

  iDestruct (inhabited_cell_states with "HAuth HInhToken")
    as %[HInh|[HRes|HAb]].

  3: {
    iDestruct (big_sepL_lookup_acc with "HCellResources") as "[HC HH]".
    eassumption.
    simpl.
    iDestruct "HC" as (?) "(_ & _ & _ & HInhToken' & _)".
    iDestruct (inhabitant_token_exclusive with "HInhToken HInhToken'")
      as ">[]".
  }

  2: {
    iDestruct (big_sepL_lookup_acc with "HCellResources") as "[HC HH]".
    eassumption.
    simpl.
    iDestruct "HC" as (?) "(>HArrMapsto' & HIsRes & HCancHandle & HIsSus & HRes)".
    iDestruct "HRes" as "[HInhToken'|[Hℓ HR]]".
    by iDestruct (inhabitant_token_exclusive with "HInhToken HInhToken'")
      as ">[]".

    iDestruct (array_mapsto'_agree with "HArrMapsto HArrMapsto'") as %<-.

    iAssert (▷ ℓ ↦ RESUMEDV ∧ ⌜val_is_unboxed RESUMEDV⌝)%I
      with "[Hℓ]" as "HAacc"; first by iFrame.

    iAaccIntro with "HAacc".
    { iIntros "[Hℓ _]". iModIntro.
      iDestruct (bi.later_wand with "HH
          [HArrMapsto' HIsRes HCancHandle HIsSus HR Hℓ]") as "$".
      by eauto with iFrame.
      iFrame. iSplitR. iFrame "HNotDone". iPureIntro; done.
      iIntros "$". done. }
    iIntros "Hℓ".
    iDestruct (bi.later_wand with "HH
        [HArrMapsto' HIsRes HCancHandle HIsSus HInhToken]") as "HCellRRs".
    by eauto with iFrame.
    iModIntro.
    iExists _. iSplitR "Hℓ HArrMapsto".
    { iLeft. iFrame. eauto. }

    iIntros "HΦ !>". by wp_pures.
  }

  repeat rewrite big_sepL_later.
  iDestruct (big_sepL_lookup_alter_abort i O (fun _ => Some (cellDone cellCancelled))
               with "[HCellResources]") as "[HCellR HCellRRsRestore]";
    simpl; try done.
  simpl.

  iDestruct "HCellR" as (?) "(>HArrMapsto' & Hℓ & >HIsSus & >HCancHandle)".
  iDestruct (array_mapsto_agree with "HArrMapsto' HArrMapsto") as %->.
  iDestruct "Hℓ" as (th) "Hℓ".

  iAssert (▷ ℓ ↦ InjLV #th ∧ ⌜val_is_unboxed (InjLV #th)⌝)%I
    with "[Hℓ]" as "HAacc". by iFrame.

  iAaccIntro with "HAacc".
  { iIntros "[Hℓ _] !>".
    repeat rewrite -big_sepL_later.
    iFrame.
    iSplitL "HCellRRsRestore Hℓ HIsSus HCancHandle".
    { iSplitR. iPureIntro; done.
      iDestruct "HCellRRsRestore" as "[HCellRRsRestore _]".
      iFrame "HNotDone".
      iApply "HCellRRsRestore".
      iExists _. iFrame "HArrMapsto". eauto with iFrame. }
    iIntros "$". done.
  }
  iIntros "Hℓ".

  remember (alter (fun _ => Some (cellDone cellCancelled)) i l) as K.

  iExists #false. iSplitL.
  2: by iIntros "!> HΦ !>"; by wp_pures.

  iRight. iFrame "HCancHandle".
  iSplitR; first done.
  iSplitR; first done.

  iDestruct "HCellRRsRestore" as "[_ HCellRRsRestore]".

  iAssert (▷ (E ∗ [∗ list] x ∈ replicate (count_matching still_present K) E, x))%I
          with "[HEs]" as "[$ $]".
  {
    subst.
    replace l with (take i l ++ (Some cellInhabited :: drop (S i) l)).
    2: by rewrite take_drop_middle.
    rewrite count_matching_app replicate_plus big_sepL_app /=.
    remember (fun _ => Some (cellDone cellCancelled)) as fn.
    remember (take _ _ ++ _) as KK.
    replace (alter fn i KK) with (alter fn (length (take i l) + 0)%nat KK).
    2: {
      rewrite -plus_n_O take_length_le //.
      assert (i < length l)%nat. 2: lia.
      apply lookup_lt_is_Some. by eexists.
    }
    subst.
    rewrite alter_app_r count_matching_app replicate_plus big_sepL_app.
    simpl.
    repeat rewrite -big_sepL_later.
    iDestruct "HEs" as "($ & $ & $)".
  }

  iAssert (⌜deqFront <= length K⌝)%I as "$".
  { iPureIntro. subst. rewrite alter_length. done. }

  rewrite /cell_list_contents_auth_ra.
  replace (length K) with (length l). 2: by subst; rewrite alter_length.

  iAssert ([∗ list] x ∈ drop deqFront K, ⌜x = Some (cellDone cellCancelled) ∨
                                         x = Some cellInhabited ∨
                                         x = None⌝)%I as "$".
  {
    subst.
    repeat rewrite big_sepL_forall.
    iIntros (k x). rewrite lookup_drop.
    destruct (decide (i = (deqFront + k)%nat)).
    {
      subst. rewrite list_lookup_alter.
      destruct (l !! _); try done.
      simpl. iIntros (HEq). simplify_eq. eauto.
    }
    rewrite list_lookup_alter_ne //. iIntros (HEq).
    iApply "HNotDone".
    rewrite lookup_drop. iPureIntro. done.
  }

  assert (forall l i, l !! i = Some (Some cellInhabited) ->
                  (map cell_state_to_RA l, replicate i ε ++ [(Excl' (), ε, ε)]) ~l~>
                  (map cell_state_to_RA
                       (alter (fun _ => Some (cellDone cellCancelled)) i l),
                   replicate i ε ++ [(ε, (3%nat: mnatUR), Some (to_agree cellCancelled))])
          ) as Hupdate_ra_map.
  { clear.
    intros l i HInh.
    apply list_lookup_local_update.
    generalize dependent i.

    induction l; first done. case; simpl.
    { intros ?. simplify_eq. simpl. case; try done. simpl.
      apply option_local_update, prod_local_update; simpl.
      2: by apply alloc_option_local_update.
      apply prod_local_update; simpl.
      by apply delete_option_local_update, excl_exclusive.
      by apply mnat_local_update; lia. }
    intros i HInh. case; try done. simpl. intros i'. eauto.
  }

  destruct (decide (i < deqFront)) as [HLt|HGt].
  {
    replace (take deqFront l)
      with (take i (take deqFront l) ++
                 Some cellInhabited :: drop (S i) (take deqFront l)).
    2: {
      rewrite take_drop_middle. done.
      rewrite lookup_take. done.
      lia.
    }
    rewrite count_matching_app replicate_plus big_sepL_app /=.
    iDestruct "HRs" as "(HRs1 & HR & HRs2)".
    iSplitL "HR".
    { iLeft. iFrame. done. }

    iMod (own_update_2 with "HAuth HInhToken") as "[HAuth HIsCanc]".
    2: iFrame "HIsCanc HAuth".
    {
      apply auth_update.
      replace (drop deqFront K) with (drop deqFront l).
      2: { subst. rewrite drop_alter. auto. lia. }
      apply prod_local_update_2.
      subst.
      by apply Hupdate_ra_map.
    }

    replace (take deqFront K)
      with (take i (take deqFront l) ++
                Some (cellDone cellCancelled) :: drop (S i) (take deqFront l)).
    2: {
      replace (take i (take deqFront l)) with (take i (take deqFront K)).
      2: {
        repeat rewrite take_take.
        replace (i `min` deqFront)%nat with i by lia.
        subst.
        by rewrite take_alter.
      }
      replace (drop (S i) (take deqFront l)) with (drop (S i) (take deqFront K)).
      2: {
        assert (S i <= deqFront)%nat as HLe by lia.
        revert HLe. rewrite nat_le_sum. case. intros c ->.
        repeat rewrite -take_drop_commute. subst.
        rewrite drop_alter. done. lia.
      }
      rewrite take_drop_middle. done.
      rewrite lookup_take. 2: lia.
      subst.
      rewrite list_lookup_alter HInh //.
    }
    rewrite count_matching_app replicate_plus big_sepL_app /=.
    repeat rewrite -big_sepL_later.
    iFrame.
    iApply "HCellRRsRestore". iFrame "HIsSus". iExists _. iFrame.
    done.
  }
  replace (take deqFront K) with (take deqFront l).
  2: { subst. rewrite take_alter; auto. lia. }
  repeat rewrite -big_sepL_later.
  iFrame "HRs".
  iDestruct ("HCellRRsRestore" with "[HArrMapsto' HIsSus Hℓ]") as "$".
  by iExists ℓ; iFrame.

  replace (count_matching (fun b => not (still_present b)) (drop deqFront K)) with
      (S (count_matching (fun b => not (still_present b)) (drop deqFront l))).
  2: {
    subst.
    assert (deqFront <= i)%nat as HLe by lia.
    revert HLe. rewrite nat_le_sum. case. intros c ->.
    rewrite drop_alter'. erewrite count_matching_alter.
    2: by rewrite lookup_drop.
    by rewrite /= -minus_n_O Nat.add_1_r.
  }
  iMod (own_update_2 with "HAuth HInhToken") as "[HAuth HFrag]".
  1: apply auth_update.
  2: iFrame "HAuth".
  {
    apply prod_local_update'; simpl.
    { apply prod_local_update_2, prod_local_update_1, nat_local_update.
      remember (count_matching _ _) as X. rewrite /ε /nat_unit.
      rewrite -plus_n_O plus_assoc_reverse.
      replace (S X) with (X + 1)%nat by lia.
      done. }
    subst.
    by eapply Hupdate_ra_map.
  }

  remember (own _ _) as X.
  iAssert (⌜X ≡ (awakening_permit γtq ∗ rendezvous_cancelled γtq i)⌝)%I as %->.
  {
    iPureIntro.
    subst. rewrite /awakening_permit /rendezvous_cancelled /rendezvous_done.
    rewrite /rendezvous_state.
    rewrite -own_op -auth_frag_op -pair_op. auto.
  }
  iDestruct "HFrag" as "[HAw $]".
  iRight. auto.
Qed.

Lemma fmap_is_map {A B} (f: A -> B) (l: list A): f <$> l = map f l.
Proof. auto. Qed.

Theorem resume_rendezvous_spec E R γa γtq γe γd i ℓ:
  inv N (cell_invariant γtq γa i ℓ) -∗
  deq_front_at_least γtq (S i) -∗
  exists_list_element γtq i -∗
  array_mapsto segment_size γa i ℓ -∗
  iterator_issued γd i -∗
  let ap := tq_ap γtq γe in
  <<< ∀ l deqFront, ▷ cell_list_contents E R γa γtq γe γd l deqFront >>>
    getAndSet #ℓ RESUMEDV @ ⊤ ∖ ↑N
  <<< ∃ v, ⌜l !! i = Some None⌝ ∧ ⌜v = NONEV⌝ ∧
             rendezvous_filled γtq i ∗
           ▷ E ∗
           ▷ cell_list_contents E R γa γtq γe γd
             (alter (fun _ => Some (cellDone cellFilled)) i l) deqFront ∨

           ⌜l !! i = Some (Some cellInhabited)⌝ ∧
           ⌜∃ (th: loc), v = InjLV #th⌝ ∧
           rendezvous_resumed γtq i ∗
           ▷ E ∗
           ▷ cell_list_contents E R γa γtq γe γd
             (alter (fun _ => Some (cellDone cellResumed)) i l) deqFront ∨

           ⌜l !! i = Some (Some (cellDone cellCancelled))⌝ ∧
           (⌜v = RESUMEDV⌝ ∨ (* can't actually happen, but it's hard to prove
                                it. *)
            ⌜v = CANCELLEDV⌝) ∧
           iterator_issued γd i ∗
           ▷ cell_list_contents E R γa γtq γe γd l deqFront ∨

           ⌜l !! i = Some (Some (cellDone cellAbandoned))⌝ ∧
           ⌜∃ (th: loc), v = InjLV #th⌝ ∧
           ▷ E ∗
             ▷ cell_list_contents E R γa γtq γe γd l deqFront,
        RET v >>>.
Proof.
  iIntros "#HCellInv #HDeqFrontLb #HExistsEl #HArrMapsto HIsRes" (Φ) "AU".

  awp_apply getAndSet_spec.
  iInv N as "HInv".
  iApply (aacc_aupd_commit with "AU"); first done.
  iIntros (l deqFront) "(>% & #HNotDone & >HAuth & HEs & HRs & HCellResources)".

  repeat rewrite big_sepL_later.
  iDestruct (exists_list_element_lookup with "HExistsEl HAuth") as %[cr HIsSome].
  destruct cr; simpl in *.
  2: {
    iDestruct "HInv" as "[[>HCancHandle >Hℓ]|>#HCellInit]".
    iDestruct (deq_front_at_least__cell_list_contents
                 with "HDeqFrontLb HAuth") as %HDeqFront.
    2: {
      iExFalso.
      rewrite /rendezvous_initialized /rendezvous_state.
      iDestruct (own_valid_2 with "HAuth HCellInit") as
          %[[_ HValid]%prod_included _]%auth_both_valid.
      iPureIntro.
      move: HValid. simpl. rewrite list_lookup_included.
      intros HValid. specialize (HValid i). rewrite map_lookup in HValid.
      rewrite HIsSome in HValid. simpl in *.
      move: HValid. clear. induction i.
      - simpl. rewrite Some_included_total prod_included; case. simpl.
        rewrite prod_included; case; simpl.
        rewrite mnat_included. lia.
      - done.
    }
    iAssert (▷ ℓ ↦ InjLV #() ∧ ⌜val_is_unboxed (InjLV #())⌝)%I with "[Hℓ]" as "HAacc".
    by iFrame.
    iAaccIntro with "HAacc".
    {
      repeat rewrite -big_sepL_later.
      iFrame "HNotDone".
      iIntros "[Hℓ _] !>". iFrame. rewrite /cell_invariant.
      iSplitR. by iPureIntro.
      iIntros "$ !>". iLeft. iFrame.
    }
    iIntros "Hℓ". iExists NONEV.

    remember (alter (fun _ => Some (cellDone cellFilled)) i l) as l'.

    iMod (own_update _ _ (● cell_list_contents_auth_ra l' deqFront ⋅
                            (◯ (ε, replicate i ε ++ [(None, cellDoneO, Some (to_agree cellFilled))]) ⋅
                             ◯ (ε, replicate i ε ++ [(None, cellDoneO, ε)]))
                         )
            with "HAuth") as "[HAuth [HFrag1 HFrag2]]".
    {
      rewrite -auth_frag_op -pair_op.
      apply auth_update_alloc. unfold cell_list_contents_auth_ra.
      replace (length l') with (length l).
      2: by subst; rewrite alter_length.
      apply prod_local_update'; simpl.
      apply prod_local_update_2.
      2: {
        repeat rewrite -fmap_is_map.
        subst.
        rewrite (list_alter_fmap
                   _ _ (fun _ => cell_state_to_RA (Some (cellDone cellFilled)))).
        2: by rewrite /= List.Forall_forall. simpl.
        apply list_lookup_local_update. intros i'.
        rewrite /ε /list_unit lookup_nil.
        destruct (nat_eq_dec i i').
        {
          subst. rewrite list_lookup_alter. repeat rewrite map_lookup.
          rewrite HIsSome. simpl.
          apply local_update_unital_discrete. intros z.
          rewrite None_op_left_id. intros _ <-. split; try done.
          clear.
          induction i'; simpl.
          2: done.
          by rewrite -Some_op -pair_op.
        }
        rewrite list_lookup_alter_ne; try done.

        apply local_update_unital_discrete. intros z. rewrite None_op_left_id.
        intros HValid <-. split; try done.
        rewrite list_lookup_op.
        rewrite list_lookup_fmap.
        destruct (decide (i' < i)) as [HLt|HGe].
        {
          repeat rewrite lookup_app_l.
          2, 3: rewrite replicate_length; lia.
          rewrite lookup_replicate_2.
          2: lia.
          assert (i < length l)%nat as HLt1.
          by apply lookup_lt_is_Some; eauto.
          assert (i' < length l)%nat as HLt2.
          lia.
          apply lookup_lt_is_Some in HLt2.
          destruct HLt2 as [? HElem].
          rewrite HElem. simpl.
          by rewrite -Some_op ucmra_unit_left_id.
        }
        {
          rewrite lookup_app_r replicate_length.
          2: lia.
          rewrite lookup_app_r replicate_length.
          2: lia.
          destruct (i' - i)%nat eqn:Z.
          lia.
          simpl.
          by rewrite lookup_nil None_op_left_id.
        }
      }
      subst.
      rewrite drop_alter. 2: lia.
      done.
    }
    iSplitR "HFrag2".
    2: {
      iIntros "!> $ !>".
      iRight.
      iApply own_mono.
      2: iApply "HFrag2".
      apply auth_included; simpl. split; try done.
      apply prod_included; simpl. split; try done.
      apply list_lookup_included. clear.
      induction i; case; try done. simpl.
      apply Some_included_total, prod_included; simpl. split; try done.
      rewrite prod_included; simpl. split; try done.
      apply mnat_included. lia.
    }
    iLeft.
    repeat (iSplitR; first done).
    rewrite /rendezvous_filled /rendezvous_done /rendezvous_state.
    iFrame "HFrag1 HAuth".
    iAssert (⌜deqFront <= length l'⌝)%I as "$".
    {
      iPureIntro. subst. rewrite alter_length. done.
    }
    subst.
    replace (alter (fun _ => Some (cellDone cellFilled)) i l)
            with (alter (fun _ => Some (cellDone cellFilled)) (length (take i l) + O)%nat l).
    2: { rewrite take_length_le. 2: lia. by rewrite -plus_n_O. }
    remember (take i l) as lln.
    replace l with (take i l ++ None :: drop (S i) l).
    2: by apply take_drop_middle.
    subst.
    rewrite alter_app_r. simpl.
    repeat rewrite take_app_ge; rewrite take_length_le; try lia.
    destruct (deqFront - i)%nat eqn:Z. lia.
    simpl.
    repeat rewrite count_matching_app; simpl. repeat rewrite replicate_plus.
    repeat rewrite big_sepL_app; simpl.
    repeat rewrite -big_sepL_later.
    iDestruct "HEs" as "(HEsH & HE & HEsT)".
    iDestruct "HRs" as "(HRsH & HR & HRsT)".
    iDestruct "HCellResources" as "(HRRsH & _ & HRRsT)".
    rewrite -plus_n_O.
    iFrame.
    repeat rewrite drop_app_ge take_length_le; try lia.
    rewrite Z. simpl. iFrame "HNotDone".
    iExists ℓ. iFrame.
    iFrame "HArrMapsto".
    iRight.
    by iFrame.
  }

  iDestruct (deq_front_at_least__cell_list_contents
                with "HDeqFrontLb HAuth") as %HDeqFront.

  destruct c.
  {
    iDestruct (big_sepL_lookup_alter_abort
                 i O (fun _ => Some (cellDone cellResumed))
                 with "[HCellResources]")
      as "[HR HCellRRsRestore]"; simpl; try done.
    simpl.
    (* remember (alter (fun _ => Some (cellDone cellResumed)) i l) as l'. *)
    iDestruct "HR" as (ℓ') "(>HArrMapsto' & HThread & HIsSus & HCancHandle)".
    iDestruct (array_mapsto_agree with "HArrMapsto' HArrMapsto") as %->.
    iDestruct "HThread" as (th) "Hℓ".
    iAssert (▷ ℓ ↦ InjLV #th ∧ ⌜val_is_unboxed (InjLV #th)⌝)%I
      with "[Hℓ]" as "HAacc".
    by iFrame.

    iAaccIntro with "HAacc".
    {
      repeat rewrite -big_sepL_later.
      iFrame "HNotDone".
      iDestruct "HCellRRsRestore" as "[HCellRRsRestore _]".
      iIntros "[Hℓ _] !>". iFrame.
      iSplitL.
      {
        iSplitR; first done.
        iApply "HCellRRsRestore".
        iExists ℓ. iFrame. eauto.
      }
      by iIntros "$ !>".
    }
    iDestruct "HCellRRsRestore" as "[_ HCellRRsRestore]".

    iIntros "Hℓ". iExists _.
    iSplitR "HInv".
    2: iFrame; by iIntros "!> $ !>".
    iRight. iLeft.

    iSplitR; first done.
    rewrite /cell_list_contents alter_length.
    iAssert (⌜deqFront <= length l⌝)%I as "$". done.
    replace (alter (fun _ => Some (cellDone cellResumed)) i l) with
      (alter (fun _ => Some (cellDone cellResumed)) (length (take i l) + O)%nat l).
    2: rewrite -plus_n_O take_length_le; first done.
    2: lia.
    remember (_ + _)%nat as K.
    replace l with (take i l ++ Some cellInhabited :: drop (S i) l).
    2: by rewrite take_drop_middle. subst.
    rewrite alter_app_r.
    repeat rewrite take_app_ge.
    all: rewrite take_length_le; try lia.
    destruct (deqFront - i)%nat eqn:Z. lia.
    repeat rewrite count_matching_app. repeat rewrite replicate_plus.
    repeat rewrite big_sepL_app. simpl.
    iDestruct "HEs" as "(HEsH & $ & HEsT)".
    iDestruct "HRs" as "(HRsH & HR & HRsT)".
    iDestruct ("HCellRRsRestore" with "[HIsRes HArrMapsto' HIsSus HCancHandle Hℓ HR]")
      as "(HCellRRsH & HCellR & HCellRRsT)".
    { iExists _. iFrame "HArrMapsto' HIsRes HCancHandle HIsSus". iRight. iFrame. }
    repeat rewrite -big_sepL_later.
    iFrame.
    unfold cell_list_contents_auth_ra.
    rewrite /rendezvous_resumed /rendezvous_done /rendezvous_state.
    iSplitR; first (iExists _; done).
    iMod (own_update with "HAuth") as "[HAuth HFrag]".
    2: {
      iFrame "HFrag HAuth".
      repeat rewrite drop_app_ge take_length_le; try lia.
      rewrite Z. simpl. done.
    }

    apply auth_update_alloc, prod_local_update'.
    {
      repeat rewrite app_length /=.
      apply prod_local_update_2.
      repeat rewrite drop_app_ge.
      all: rewrite take_length_le; try lia.
      rewrite Z. simpl.
      done.
    }

    repeat rewrite -fmap_is_map. repeat rewrite fmap_app. simpl.
    assert (i < length l)%nat as HLt by lia.
    apply list_lookup_local_update. intros i'.
    destruct (decide (i' < i)%nat) as [HLti'|HGei'].
    - repeat rewrite lookup_app_l. rewrite lookup_nil.
      rewrite list_lookup_fmap. rewrite lookup_take.
      rewrite lookup_replicate_2.
      all: try rewrite replicate_length.
      all: try rewrite fmap_length take_length_le.
      all: try lia.
      assert (i' < length l)%nat as HLti'_len by lia.
      revert HLti'_len. rewrite -lookup_lt_is_Some.
      case. intros ? HEl. rewrite HEl. simpl.
      apply option_local_update'. done.
    - repeat rewrite lookup_app_r.
      all: try rewrite replicate_length.
      all: try rewrite fmap_length take_length_le.
      all: try lia.
      destruct (decide (i' = i)); subst.
      2: {
        destruct (i' - i)%nat eqn:Y. lia.
        simpl. by repeat rewrite lookup_nil.
      }
      rewrite minus_diag. simpl. rewrite lookup_nil.
      apply option_local_update'.
      apply prod_local_update'; simpl.
      2: by apply alloc_option_local_update.
      apply prod_local_update_2, mnat_local_update. lia.
  }

  iDestruct (big_sepL_lookup_acc with "[HCellResources]")
    as "[HR HCellRRsRestore]"; simpl; try done.
  simpl.

  repeat rewrite -big_sepL_later.
  destruct c; simpl.
  2: {
    iDestruct "HR" as (?) "(_ & >HIsRes' & _)".
    iDestruct (iterator_issued_exclusive with "HIsRes HIsRes'") as %[].
  }
  2: {
    iDestruct "HR" as (?) "(_ & >HIsRes' & _)".
    iDestruct (iterator_issued_exclusive with "HIsRes HIsRes'") as %[].
  }

  {
    iDestruct "HR" as (ℓ') "(>HArrMapsto' & HIsSus & HVal)".
    iDestruct (array_mapsto_agree with "HArrMapsto' HArrMapsto") as %->.
    iAssert (∃ v, (⌜v = CANCELLEDV \/ v = RESUMEDV⌝) ∧ ▷ ℓ ↦ v)%I
            with "[HVal]" as (v HVal) "Hℓ".
    {
      iDestruct "HVal" as "[HVal|HVal]"; iExists _; iFrame; iPureIntro; auto.
    }
    iAssert (▷ ℓ ↦ v ∧ ⌜val_is_unboxed v⌝)%I with "[Hℓ]" as "HAacc".
    { iFrame. iPureIntro. destruct HVal; subst; done. }
    iAaccIntro with "HAacc"; iFrame "HNotDone".

    {
      iIntros "[Hℓ _]". iSplitR "HInv HIsRes". iFrame.
      iSplitR; first done. iApply "HCellRRsRestore".
      { iExists _. iFrame "HArrMapsto'". iFrame.
        destruct HVal; subst; eauto. }
      iIntros "!> $ !>"; iFrame.
    }

    iIntros "Hℓ !>". iExists v. iSplitR "HInv".
    2: by iIntros "$ !>".
    iRight. iRight. iLeft.

    iSplitR; first done.
    iSplitR.
    { iPureIntro. destruct HVal; auto. }
    iFrame.
    iSplitR; first done.
    iApply "HCellRRsRestore".
    iExists _; iFrame "HArrMapsto'". iFrame.
  }

  iDestruct "HR" as (?) "(>HArrMapsto' & HCancHandle & HIsSus & HInh & HDeqFront & HH)".
  iDestruct "HH" as "[>HIsRes'|[HThread HE]]".
  by iDestruct (iterator_issued_exclusive with "HIsRes HIsRes'") as %[].
  iDestruct (array_mapsto_agree with "HArrMapsto' HArrMapsto") as %->.
  iDestruct "HThread" as (v) "Hℓ".

  iAssert (▷ ℓ ↦ InjLV #v ∧ ⌜val_is_unboxed (InjLV #v)⌝)%I
    with "[Hℓ]" as "HAacc".
  by iFrame.

  iAaccIntro with "HAacc"; iFrame "HNotDone".
  {
    iIntros "[Hℓ _] !>".
    iSplitR "HInv HIsRes".
    {
      iFrame. iSplitR; first done. iApply "HCellRRsRestore".
      iExists _; iFrame "HArrMapsto'"; iFrame.
      iRight. iFrame. by iExists _.
    }
    iIntros "$ !>". iFrame.
  }

  iIntros "Hℓ !>". iExists _.
  iSplitR "HInv".
  2: by iIntros "$ !>".
  repeat iRight.

  iSplitR; first done.
  iSplitR; first by eauto.
  iFrame.
  iSplitR; first done.
  iApply "HCellRRsRestore".
  iExists _; iFrame "HArrMapsto'". iFrame.
Qed.

Lemma list_lookup_local_update' {A: ucmraT}:
  forall (x y x' y': list A),
    (forall i, (x !! i, y !! i) ~l~> (x' !! i, y' !! i)) ->
    (x, y) ~l~> (x', y').
Proof.
  intros x y x' y' Hup.
  apply local_update_unital=> n z Hxv Hx.
  unfold local_update in Hup.
  simpl in *.
  assert (forall i, ✓{n} (x' !! i) /\ x' !! i ≡{n}≡ (y' ⋅ z) !! i) as Hup'.
  { intros i. destruct (Hup i n (Some (z !! i))); simpl in *.
    - by apply list_lookup_validN.
    - rewrite -list_lookup_op.
      by apply list_dist_lookup.
    - rewrite list_lookup_op. split; done.
  }
  split; [apply list_lookup_validN | apply list_dist_lookup].
  all: intros i; by destruct (Hup' i).
Qed.

Lemma list_validN_app {A: ucmraT} (x y : list A) (n: nat):
  ✓{n} (x ++ y) <-> ✓{n} x ∧ ✓{n} y.
Proof. apply Forall_app. Qed.

Lemma list_app_l_local_update {A: ucmraT}:
  forall (x y y' z: list A),
    (y, ε) ~l~> (y', z) ->
    (x ++ y, ε) ~l~> (x ++ y', (replicate (length x) ε) ++ z).
Proof.
  intros ? ? ? ? HUp.
  apply local_update_unital=> n mz Hxv Hx.
  unfold local_update in HUp. simpl in *.
  specialize (HUp n (Some y)).
  simpl in *.
  move: HUp Hx.
  repeat rewrite ucmra_unit_left_id.
  move=> HUp <-.
  apply list_validN_app in Hxv. destruct Hxv as [Hxv Hyv].
  specialize (HUp Hyv).
  rewrite list_validN_app.
  destruct HUp as [Hy'v Hy'eq].
  auto.
  repeat split; try done.
  rewrite Hy'eq.
  apply list_dist_lookup.
  intros i.
  rewrite list_lookup_op.
  destruct (decide (i < length x)%nat) as [HLt|HGe].
  {
    repeat rewrite lookup_app_l.
    all: (try rewrite replicate_length); try lia.
    2: assumption. (* why doesn't lia work ??? *)
    rewrite lookup_replicate_2; try lia.
    apply lookup_lt_is_Some in HLt.
    destruct HLt as (? & HEl).
    by rewrite HEl -Some_op ucmra_unit_left_id.
  }
  {
    assert (length x <= i)%nat as HLe by lia.
    repeat rewrite lookup_app_r.
    all: try rewrite replicate_length.
    all: try lia.
    2: assumption.
    remember (i - length _)%nat as K. clear.
    by rewrite list_lookup_op.
  }
Qed.

Lemma list_app_r_local_update {A: ucmraT}:
  forall (x x' y y': list A),
    length x = length x' ->
    (x, ε) ~l~> (x', y') ->
    (x ++ y, ε) ~l~> (x' ++ y, y').
Proof.
  intros ? ? ? ? HLen HUp.
  apply local_update_unital=> n mz Hxv.
  rewrite ucmra_unit_left_id. move=> <-.
  specialize (HUp n (Some x)); simpl in *.
  apply list_validN_app in Hxv. destruct Hxv as [Hxv Hyv].
  destruct HUp as [Hx'v Hx'Eq]; auto.
  split.
  by apply list_validN_app.
  rewrite Hx'Eq.
  assert (length y' <= length x)%nat as Hy'Len.
  {
    assert (length x = length (y' ⋅ x)) as ->.
    by rewrite -Hx'Eq.
    rewrite list_op_length.
    lia.
  }
  symmetry.
  rewrite mixin_cmra_comm.
  rewrite list_op_app_le.
  rewrite mixin_cmra_comm.
  all: try done.
  apply list_cmra_mixin.
  apply list_cmra_mixin.
Qed.

Theorem abandon_rendezvous E R γa γtq γe γd l deqFront i:
  deq_front_at_least γtq (S i) -∗
  inhabitant_token γtq i -∗
  cell_list_contents E R γa γtq γe γd l deqFront ==∗
  (⌜l !! i = Some (Some cellInhabited)⌝ ∧
  cell_list_contents E R γa γtq γe γd
                    (alter (fun _ => Some (cellDone cellAbandoned)) i l) deqFront ∗
                    rendezvous_abandoned γtq i ∨
  ⌜l !! i = Some (Some (cellDone cellResumed))⌝ ∧
  cell_list_contents E R γa γtq γe γd l deqFront) ∗ R.
Proof.
  iIntros "#HDeqFront HInhToken HContents".
  rewrite /cell_list_contents.
  iDestruct "HContents" as (HDfLeLL) "(#HNotDone & HAuth & HEs & HRs & HRRs)".
  iFrame "HNotDone".
  rewrite alter_length.
  iDestruct (deq_front_at_least__cell_list_contents with "HDeqFront HAuth")
            as %HLb.
  assert (i < length l)%nat as HLt by lia.
  apply lookup_lt_is_Some in HLt. destruct HLt as [v HEl].
  iAssert (⌜v = Some cellInhabited \/ v = Some (cellDone cellResumed)
           \/ v = Some (cellDone cellAbandoned)⌝)%I
    with "[HAuth HInhToken]" as %HV.
  {
    iDestruct (own_valid_2 with "HAuth HInhToken")
      as %[[_ HValid]%prod_included _]%auth_both_valid.
    simpl in *.
    iPureIntro. move: HValid. rewrite list_lookup_included.
    intros HValid. specialize (HValid i). move: HValid.
    rewrite map_lookup HEl /=.
    remember (_, ε) as K. replace (_ !! i) with (Some K); subst.
    2: clear; by induction i.
    rewrite Some_included_total prod_included /=. case.
    intros HValid _. move: HValid. rewrite prod_included /=. case.
    intros HValid _.
    assert ((cell_state_to_RA v).1.1 = None -> False) as HH.
    {
      move: HValid.
      rewrite option_included; case; first done.
      intros (a & b & HV1 & HV2 & HV3). rewrite HV2.
      discriminate.
    }

    destruct v as [v'|]; simpl in *.
    2: contradiction.
    destruct v' as [|v'']; simpl in *; first by auto.
    destruct v''; simpl in *; try contradiction.
    all: by auto.
  }

  destruct HV as [HV|[HV|HV]]; subst.
  {
    remember (alter _ i l) as K.
    replace (take deqFront K)
      with (take deqFront
                 (take i K ++ Some (cellDone cellAbandoned) :: drop (S i) K)).
    2: {
      rewrite take_drop_middle; first done. subst.
      by rewrite list_lookup_alter HEl.
    }
    replace (take deqFront l) with (take deqFront (take i l ++ Some cellInhabited :: drop (S i) l)).
    2: by rewrite take_drop_middle.
    subst.
    repeat rewrite take_app_ge take_length_le; try lia.
    all: try by (rewrite alter_length; lia).
    destruct (deqFront - i)%nat eqn:X. lia.
    rewrite take_alter. 2: done. repeat rewrite drop_alter. all: try lia.
    iFrame "HNotDone".
    simpl. repeat rewrite count_matching_app replicate_plus /=.
    iDestruct "HRs" as "($ & $ & $)".

    iLeft. iSplitR; first by iPureIntro.
    iAssert (⌜deqFront <= length l⌝)%I as "$"; first by iPureIntro; lia.

    replace l with (take i l ++ Some cellInhabited :: drop (S i) l).
    2: by rewrite take_drop_middle.

    rewrite alter_app_r_alt take_length_le.
    all: try lia.
    repeat rewrite minus_diag.

    repeat rewrite count_matching_app replicate_plus big_sepL_app.
    iDestruct "HEs" as "($ & HE & $)".
    iDestruct "HRRs" as "($ & HRr & $)".

    rewrite take_length_le; try lia.
    rewrite -plus_n_O. simpl.

    iDestruct "HRr" as (?) "(HArrMapsto & HLoc & $ & $)".

    iMod (own_update with "HAuth") as "[HAuth HFrag]".
    2: iFrame "HDeqFront HAuth HInhToken HFrag".
    2: iExists _; iFrame "HArrMapsto"; iRight; by iFrame.

    apply auth_update_alloc, prod_local_update'; simpl.
    {
      repeat rewrite app_length /=. apply prod_local_update_2; simpl.
      apply prod_local_update_1.
      repeat rewrite drop_app_ge.
      all: rewrite take_length_le; try lia.
      by rewrite X /=.
    }

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
    apply mnat_local_update.
    lia.
  }
  {
    iDestruct (big_sepL_lookup_acc with "HRRs") as "[HR HRRs]"; first done.
    simpl.
    iDestruct "HR" as (?) "(HArrMapsto & HIsRes & HCancHandle & HIsSus & HH)".
    iDestruct "HH" as "[HInhToken'|[Hℓ HR']]".
    by iDestruct (inhabitant_token_exclusive with "HInhToken HInhToken'") as %[].
    iFrame "HR'".
    iRight. repeat (iSplitR; first by iPureIntro).
    iFrame.
    iApply "HRRs". iExists _; by iFrame.
  }
  {
    iExFalso.
    iDestruct (big_sepL_lookup_acc with "HRRs") as "[HR HRRs]"; first done.
    simpl.
    iDestruct "HR" as (?) "(_ & _ & _ & HInhToken' & _)".
    by iDestruct (inhabitant_token_exclusive with "HInhToken HInhToken'") as %[].
  }
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
  apply mnat_included; lia.
Qed.

Lemma read_iterator γa γ ℓ pℓ v:
  iterator_points_to segment_size γa γ ℓ pℓ v ==∗
  ∃ (id: nat) (ℓ': loc), ⌜(id * Pos.to_nat segment_size <= v)%nat⌝ ∗ pℓ ↦ #ℓ' ∗
                          segment_location γa id ℓ' ∗
                          iterator_counter_at_least γ v ∗
                          (pℓ ↦ #ℓ' -∗ iterator_points_to segment_size γa γ ℓ pℓ v).
Proof.
  iIntros "(HCounter & HSeg)".
  iDestruct "HSeg" as (id HLe ℓ') "(#HSegLoc & Hpℓ)".
  iExists id, ℓ'. iFrame "Hpℓ".
  iSplitR; first done. iFrame "HSegLoc".
  iMod (iterator_counter_is_at_least with "HCounter") as "[$ $]".
  iIntros "!> Hpℓ". iExists id.
  iSplitR; first done. iExists _; iFrame "HSegLoc Hpℓ".
Qed.

Lemma nat_lt_sum (x y: nat):
  (x < y)%nat <-> (exists z, y = x + S z)%nat.
Proof.
  rewrite -Nat.le_succ_l nat_le_sum /=.
  split; case; intros ? ->; eexists; by rewrite -plus_n_Sm.
Qed.

Lemma cancelled_cell_is_cancelled_rendezvous' S R γa γtq γe γd i l deqFront:
  cell_is_cancelled segment_size γa i -∗
  rendezvous_initialized γtq i -∗ cell_list_contents S R γa γtq γe γd l deqFront -∗
  ⌜l !! i = Some (Some (cellDone cellCancelled))⌝.
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
    simpl in *. move: HValid. rewrite Some_included_total prod_included.
    rewrite prod_included mnat_included.
    case; intros [_ HValid] _. simpl in *.
    lia.
  }
  iDestruct (big_sepL_lookup with "HRRs") as "HR"; first done.
  simpl.
  iDestruct "HR" as (?) "[_ HR]".
  destruct s'.
  1: iDestruct "HR" as "(_ & _ & HCancHandle)".
  2: destruct c; auto.
  2: iDestruct "HR" as "(_ & HCancHandle & _)".
  3: iDestruct "HR" as "(_ & HCancHandle & _)".
  4: iDestruct "HR" as "(HCancHandle & _)".
  all: by iDestruct (cell_cancellation_handle'_not_cancelled with "HCancHandle HCanc")
      as %[].
Qed.

Lemma cancelled_cell_is_cancelled_rendezvous S R γa γtq γe γd ℓ i l deqFront:
  cell_is_cancelled segment_size γa i -∗
  cell_invariant γtq γa i ℓ -∗ cell_list_contents S R γa γtq γe γd l deqFront -∗
  ⌜l !! i = Some (Some (cellDone cellCancelled))⌝.
Proof.
  iIntros "HCanc HCellInv HListContents".
  iDestruct "HCellInv" as "[[HCancHandle _]|HInit]".
  by iDestruct (cell_cancellation_handle'_not_cancelled with "HCancHandle HCanc")
    as %[].
  by iApply (cancelled_cell_is_cancelled_rendezvous' with "HCanc HInit").
Qed.

Theorem increase_deqIdx E R γa γtq γe γd (eℓ epℓ dℓ dpℓ: loc):
  ▷ awakening_permit γtq -∗ ∀ Φ,
  AU << ∀ l deqFront, ▷ is_thread_queue E R γa γtq γe γd eℓ epℓ dℓ dpℓ l deqFront >>
  @ ⊤, ↑N
  << ▷ is_thread_queue E R γa γtq γe γd eℓ epℓ dℓ dpℓ l deqFront, COMM Φ #() >> -∗
  WP ((iterator_step_skipping_cancelled segment_size) #dpℓ) #dℓ {{ v, Φ v }}.
Proof.
  iIntros "HAwaken" (Φ) "AU". iLöb as "IH".

  wp_lam. wp_pures. wp_bind (!_)%E.

  iMod "AU" as (? ?) "[(HInfArr & HListContents & HCancA & HRest) [HClose _]]".
  iDestruct "HRest" as (? deqIdx) "(HEnqIt & >HDeqIt & HRest)".
  iMod (read_iterator with "HDeqIt") as
      (hId hℓ Hhl) "(Hpℓ & #HSegLoc & #HCounter & HRestore)".
  wp_load.
  iMod ("HClose" with "[HInfArr HListContents HEnqIt HCancA HRest Hpℓ HRestore]") as "AU".
  { iFrame "HInfArr HListContents HCancA".
    iDestruct ("HRestore" with "Hpℓ") as "HIterator".
    iExists _, deqIdx. by iFrame.
  }

  iModIntro. wp_pures.
  wp_bind (FAA _ _).
  awp_apply iterator_value_faa. iApply (aacc_aupd_abort with "AU"); first done.
  iIntros (? deqFront) "(HInfArr & HListContents & HCancA & HRest)".
  iDestruct "HRest" as (? deqIdx') "(HEnqIt & >HDeqIt & >HRest)".
  iDestruct (iterator_points_to_at_least with "HCounter [HDeqIt]") as %HLet.
  by iDestruct "HDeqIt" as "[$ _]".
  (* Here I must prove that deqIdx' + 1 <= deqFront *)
  iDestruct "HRest" as "[HRest HRest']".

  iDestruct (awakening_permit_implies_bound 1
               with "[HRest'] [HAwaken] [HDeqIt] HRest HListContents HCancA")
    as "#>%".
  by iDestruct "HRest'" as "%"; iPureIntro; lia.
  by iFrame.
  by iDestruct "HDeqIt" as "[$ _]".

  iAaccIntro with "HDeqIt".
  { iIntros "HIsIter". iFrame "HInfArr HListContents HCancA".
    iSplitL "HEnqIt HRest HRest' HIsIter".
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

  iFrame "HInfArr HListContents HCancA".
  iSplitR "HPerms".
  { iExists _, _. iFrame.
    rewrite seq_add big_sepL_app.
    iDestruct "HRest'" as "([% %] & %)".
    simpl.
    iFrame.
    iPureIntro.
    repeat split; try done.
    lia.
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
    assert (hId = deqIdx' `div` Pos.to_nat segment_size)%nat as ->.
    { eapply find_segment_id_bound; try lia. done. }
    iRight. iIntros "!> HΦ !>". wp_pures. rewrite bool_decide_eq_true_2 //.
    wp_pures.
    (* I need to provide proper return predicates. *)
    admit.
  }

  destruct (decide (tId = (deqIdx' `div` Pos.to_nat segment_size)%nat)).
  {
    iRight. iIntros "!> HΦ !>". wp_pures. rewrite bool_decide_eq_true_2.
    2: by subst.
    wp_pures.
    admit.
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
  iIntros "!> AU !>".

  wp_pures. rewrite -Nat2Z.inj_mul.
  awp_apply increase_value_to_spec. iApply (aacc_aupd_abort with "AU"); first done.
  iIntros (l ?) "(HInfArr & HListContents & HCancA & HRest)".
  iDestruct "HRest" as (? deqIdx'') "(HEnqIt & >HDeqIt & HRest)".
  iDestruct (iterator_points_to_at_least with "HCounter [HDeqIt]") as "%".
  by iDestruct "HDeqIt" as "[$ _]".
  iDestruct "HDeqIt" as "[HDeqCounter HDeqLoc]".
  iAaccIntro with "HDeqCounter".
  {
    iFrame "HPerms".
    iIntros "HDeqCounter !>". iSplitL.
    * iFrame "HInfArr HListContents HCancA".
      iExists _, _. iFrame "HEnqIt HRest". by iFrame.
    * by iIntros "$".
  }

  iIntros "[HPerms' HV]". iFrame "HInfArr".
  rewrite segments_cancelled__cells_cancelled.

  (* I need to get my acquire permit back from the cancelled segment. *)
  (* First, I need to learn that my cell is truly cancelled. *)
  remember (deqIdx' `div` Pos.to_nat segment_size)%nat as deqSeg.
  iAssert ([∗ list] id ∈ seq deqIdx' (tId * Pos.to_nat segment_size - deqIdx'),
           (∃ ℓ, inv N (cell_invariant γtq γa id ℓ)) ∗ cell_is_cancelled segment_size γa id)%I
          as "#HEv".
  {
    repeat rewrite big_sepL_forall.
    iIntros (k x HEv).
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

  iDestruct "HV" as "[[% HDeqCounter]|[% HDeqCounter]]".
  {
    iDestruct ("HEv" $! O with "[]") as "[HInv #HCanc]".
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
    iDestruct "HInv" as (?) "#HInv".
    iInv N as ">HOpen" "HClose". rewrite -plus_n_O.
    iDestruct (cancelled_cell_is_cancelled_rendezvous with
                   "HCanc HOpen HListContents") as "#>%".
    iDestruct "HRest" as "(HAwak & >[[% %] %])".
    repeat rewrite big_sepL_later.
    iDestruct (big_sepL_lookup_acc with "HCancA")
      as "[HXCanc HCancRestore]".
    eassumption. simpl.
    iDestruct "HXCanc" as "[HAwaken|>HContra]".
    2: by iDestruct (iterator_issued_exclusive with "HPerms HContra") as %[].
    iDestruct ("HCancRestore" with "[HPerms]") as "HCanc'". by iRight.
    iMod ("HClose" with "HOpen") as "_".
    iSplitR "HAwaken".
    2: {
      iIntros "!> AU !>". wp_pures.
      by iApply ("IH" with "HAwaken AU").
    }
    iFrame "HListContents".
    repeat rewrite -big_sepL_later. iFrame "HCanc'".
    iExists _, _. iFrame.
    by iPureIntro.
  }

  assert (deqIdx' < deqIdx'')%nat as HL by lia.
  apply nat_lt_sum in HL. destruct HL as (d & ->).

  iAssert ([∗ list] i ∈ seq (deqIdx' + S d)
                    (tId * Pos.to_nat segment_size - (deqIdx' + S d)),
           iterator_issued γd i)%I with "[HPerms']" as "HIsss".
  {
    iClear "IH HSegLoc HCounter HSegLoc' HEv".
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
    rewrite -mnat_op_max -gset_disj_union.
    2: by apply set_seq_S_start_disjoint.
    rewrite pair_op auth_frag_op own_op.
    iDestruct "HPerms'" as "[$ HRec]".
    change (S (start + (deqIdx' + S d)))%nat with
        ((1 + start) + (deqIdx' + S d))%nat.
    iApply ("IH" with "[] [HRec]").
    2: by rewrite mnat_op_max /= -HEqX.
    iPureIntro.
    simpl. lia.
  }

  iAssert (□ [∗ list] k ∈ seq deqIdx' (tId * Pos.to_nat segment_size - deqIdx')%nat,
           |={↑N}=> cell_is_cancelled segment_size γa k ∗ rendezvous_initialized γtq k)%I
  as "#HEv'".
  {
    iIntros "!>".
    remember (seq _ _) as l'.
    iClear "IH HSegLoc HCounter HSegLoc'". clear.
    iInduction l' as [|x l'] "IH"; simpl; first done.
    iDestruct ("HEv" $! O with "[]") as "[HInv HCanc]"; first by eauto.
    iDestruct "HInv" as (?) "#HInv".
    iSplitL.
    2: {
      iApply "IH".
      iIntros "!>" (k ? HEl).
      iApply ("HEv" $! (S k) a).
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
  iDestruct "HEv'" as ">#HEv'".

  iAssert ([∗ list] k ∈ seq deqIdx' (tId * Pos.to_nat segment_size - deqIdx'),
          ▷ ⌜l !! k = Some (Some (cellDone cellCancelled))⌝)%I as "#HEv''".
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

  iDestruct "HRest" as "(HRest' & >%)".

  iDestruct (big_sepL_lookup _ _ O with "HEv''") as %HEl.
  by apply seq_lookup; lia.
  rewrite -plus_n_O in HEl.

  iDestruct (big_sepL_lookup_acc _ _ deqIdx' with "HCancA")
    as "[HXCanc HCancRestore]".
  eassumption.
  simpl. iDestruct "HXCanc" as "[HAwak|>HIsSus']".
  2: by iDestruct (iterator_issued_exclusive with "HPerms HIsSus'") as %[].
  iDestruct ("HCancRestore" with "[HPerms]") as "HCancA"; first by eauto.

  iAssert (▷(([∗ list] i ∈ seq (deqIdx' + S d)
                     (tId * Pos.to_nat segment_size - (deqIdx' + S d)),
            awakening_permit γtq) ∗
           ([∗ list] i ↦ b ∈ l, match b with
                                 | Some (cellDone cellCancelled) =>
                                   awakening_permit γtq ∨ iterator_issued γd i
                                 | _ => True
                                 end)))%I
  with "[HCancA HIsss]" as "[>HAwaks $]".
  {
    iClear "IH HEv HSegLoc HCounter HSegLoc' HEv'".
    iAssert (⌜tId * Pos.to_nat segment_size <= length l⌝)%I as "%".
    {
      iDestruct (big_sepL_lookup
                   _ _ (tId * Pos.to_nat segment_size - deqIdx' - 1)%nat
                   with "HEv''") as "HH".
      by apply seq_lookup; lia.
      iDestruct "HH" as %HH.
      assert (tId * Pos.to_nat segment_size - 1 < length l)%nat.
      {
        replace (deqIdx' + (_ - _))%nat with
            (tId * Pos.to_nat segment_size - 1)%nat in HH by lia.
        apply lookup_lt_is_Some; eauto.
      }
      iPureIntro; lia.
    }
    replace l with (take (deqIdx' + S d)%nat l ++ drop (deqIdx' + S d)%nat l).
    2: by rewrite take_drop.
    rewrite big_sepL_app.
    iDestruct "HCancA" as "[$ HCancA]".
    replace (drop (deqIdx' + S d) l) with
        (take (tId * Pos.to_nat segment_size - (deqIdx' + S d))
              (drop (deqIdx' + S d) l)
       ++ drop (tId * Pos.to_nat segment_size - (deqIdx' + S d))
              (drop (deqIdx' + S d) l)
        ).
    2: by rewrite take_drop.
    rewrite big_sepL_app.
    iDestruct "HCancA" as "[HCancA $]".

    rewrite big_sepL_later.
    remember (tId * Pos.to_nat segment_size - (deqIdx' + S d))%nat as len.
    remember (deqIdx' + S d)%nat as start.
    assert (start + len <= length l) as HOk.
    by subst; lia.

    iAssert (∀ i, ⌜(i < len)%nat⌝ -∗ ⌜drop start l !! i =
            Some (Some (cellDone cellCancelled))⌝)%I as "#HEv'''".
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
      rewrite <- HH.
      congr (fun x => l !! x).
      lia.
    }

    iClear "HEv''".

    move: HOk.
    clear.
    intros HOk.

    rewrite take_length_le. 2: lia.

    remember (drop start l) as l'.
    assert (len <= length l')%nat as HOk'.
    by subst; rewrite drop_length; lia.

    clear HOk Heql' l.

    iInduction len as [|len'] "IH" forall (l' HOk' start); simpl in *; first done.
    destruct l' as [|x l']; first by inversion HOk'. simpl in *.
    iDestruct "HCancA" as "[HR HCancA]".
    iDestruct "HIsss" as "[HItIss HIsss]".
    iDestruct ("IH" with "[] [] [HCancA] HIsss") as "[$ HHH']".
    3: {
      iApply (big_sepL_mono with "HCancA").
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
    iDestruct ("HEv'''" $! O with "[]") as %HIsCanc.
    by iPureIntro; lia.
    simpl in *.
    simplify_eq.
    rewrite -plus_n_O.
    iDestruct "HR" as "[$|HItIss']".
    by eauto.
    iDestruct (iterator_issued_exclusive with "HItIss HItIss'") as ">%".
    done.
  }

  iSplitR "HAwak".
  2: {
    iIntros "!> AU !>". wp_pures.
    iApply ("IH" with "HAwak AU").
  }

Abort.

End proof.
