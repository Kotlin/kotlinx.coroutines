From iris.heap_lang Require Import notation.

Require Import SegmentQueue.lib.infinite_array.infinite_array_impl.
Require Import SegmentQueue.lib.infinite_array.iterator.
Require Import SegmentQueue.lib.util.getAndSet.
Require Import SegmentQueue.lib.util.interruptibly.

Notation RESUMEDV := (SOMEV #0).
Notation CANCELLEDV := (SOMEV #1).

Lemma big_sepL_forall' {PROP: bi} {A B: Type}
      (f: nat -> A -> PROP) (g: nat -> B -> PROP)
      (l: list A) (l': list B):
  strings.length l = strings.length l' ->
  (∀ (k : nat) y y', l !! k = Some y → l' !! k = Some y' → f k y ≡ g k y') ->
  ([∗ list] k ↦ y ∈ l, f k y)%I ≡ ([∗ list] k ↦ y ∈ l', g k y)%I.
Proof. intros. apply big_opL_forall'; eauto; try apply _. Qed.

Section impl.

Variable segment_size: positive.

Definition cancel_cell: val :=
  λ: "cell'", let: "cell" := cell_ref_loc "cell'" in
              if: getAndSet "cell" CANCELLEDV = RESUMEDV
              then #false
              else segment_cancell_cell segment_size (Fst "cell'") ;; #true.

Definition move_ptr_forward : val :=
  rec: "loop" "ptr" "seg" := let: "curSeg" := !"ptr" in
                             if: segment_id "seg" ≤ segment_id "curSeg"
                             then #() else
                               if: CAS "ptr" "curSeg" "seg"
                               then #() else "loop" "ptr" "seg".

Definition park: val :=
  λ: "cancellationHandler" "cancHandle" "threadHandle",
  let: "r" := interruptibly "cancHandle"
                            (λ: "c", if: ! "c" then NONEV else SOMEV #())%V
                            "cancellationHandler"
                            "threadHandle" in
  if: (Fst "r")
  then #true
  else "threadHandle" <- #true ;; #false.

Definition unpark: val :=
  λ: "threadHandle", "threadHandle" <- #false.

Definition try_enque_thread: val :=
  λ: "threadHandle" "tail" "enqIdx",
  let: "cell'" := (iterator_step segment_size) "tail" "enqIdx" in
  move_ptr_forward "tail" (Fst "cell'") ;;
  let: "cell" := cell_ref_loc "cell'" in
  if: getAndSet "cell" (InjL "threadHandle") = RESUMEDV
  then NONE
  else SOME "cell'".

Definition suspend: val :=
  λ: "handler" "cancHandle" "threadHandle" "tail" "enqIdx",
  match: try_enque_thread "threadHandle" "tail" "enqIdx" with
    NONE => #false
  | SOME "cell'" =>
    park ("handler" (λ: <>, cancel_cell "cell'")) "cancHandle" "threadHandle"
  end.

Definition try_deque_thread: val :=
  rec: "resume" "head" "deqIdx" :=
    let: "cell'" := (iterator_step_skipping_cancelled segment_size)
                      "head" "deqIdx" in
    segment_cutoff (Fst "cell'") ;;
    move_ptr_forward "head" (Fst "cell'") ;;
    let: "cell" := cell_ref_loc "cell'" in
    let: "p" := getAndSet "cell" RESUMEDV in
    if: "p" = CANCELLEDV
    then "resume" "head" "deqIdx"
    else match: "p" with
        InjL "x" => "x"
      | InjR "x" => "impossible"
    end.

Definition resume: val :=
  λ: "head" "deqIdx",
  let: "x" := try_deque_thread "head" "deqIdx" in
  if: "x" = #()
  then #()
  else unpark "x" ;; #().

Definition new_thread_queue: val :=
  λ: <>, let: "arr" := new_infinite_array segment_size #() in
         let: "hd" := ref "arr" in
         let: "tl" := ref "arr" in
         let: "enqIdx" := ref #0 in
         let: "deqIdx" := ref #0 in
         (("hd", "enqIdx"), ("tl", "deqIdx")).

End impl.

From iris.heap_lang Require Import proofmode.
From iris.algebra Require Import auth.

Section parking.

Notation algebra := (authUR (prodUR
                               (optionUR (prodR fracR (agreeR boolO)))
                               (optionUR (agreeR locO)))).

Class parkingG Σ := ParkingG { parking_inG :> inG Σ algebra }.
Definition parkingΣ : gFunctors := #[GFunctor algebra].
Instance subG_parkingΣ {Σ} : subG parkingΣ Σ -> parkingG Σ.
Proof. solve_inG. Qed.

Context `{heapG Σ} `{parkingG Σ} `{interruptiblyG Σ}.
Variable N: namespace.

Definition thread_handle_in_state (γ: gname) (v: loc) (x: bool): iProp Σ :=
  (v ↦ #x ∗ own γ (● (Some (1%Qp, to_agree x), Some (to_agree v))))%I.

Definition is_thread_handle (γ: gname) (v: val) :=
  inv N (∃ (ℓ: loc) x, ⌜v = #ℓ⌝ ∗ thread_handle_in_state γ ℓ x)%I.

Definition thread_handler (γ: gname) (q: Qp) (x: bool): iProp Σ :=
  own γ (◯ (Some (q, to_agree x), None)).

Theorem thread_update_state γ (ℓ: loc) (x'': bool):
  is_thread_handle γ #ℓ -∗
  <<< ∀ x', ▷ thread_handler γ 1 x' >>>
    #ℓ <- #x'' @ ⊤ ∖ ↑N
  <<< thread_handler γ 1 x'', RET #() >>>.
Proof.
  iIntros "#HInv" (Φ) "AU".
  iInv "HInv" as "HIsHandle" "HInvClose".
  iMod "AU" as (x') "[HFrag [_ HClose]]".
  iDestruct "HIsHandle" as (? ?) "[>% [HLoc HAuth]]". simplify_eq.
  wp_store.
  iMod (own_update_2 with "HAuth HFrag") as "[HAuth HFrag]".
  { by apply auth_update, prod_local_update_1, option_local_update,
      (exclusive_local_update _ (1%Qp, to_agree x'')). }
  iMod ("HClose" with "HFrag") as "HΦ".
  iModIntro.
  iMod ("HInvClose" with "[-HΦ]") as "_".
  by iExists _, _; iFrame.
  by iFrame.
Qed.

Definition thread_has_permit γ := thread_handler γ 1 false.
Definition thread_doesnt_have_permits γ := thread_handler γ 1 true.

Theorem unpark_spec γ (ℓ: loc):
  is_thread_handle γ #ℓ -∗
  <<< ▷ thread_doesnt_have_permits γ >>>
      unpark #ℓ @ ⊤ ∖ ↑N
  <<< thread_has_permit γ, RET #() >>>.
Proof.
  iIntros "HInv" (Φ) "AU". wp_lam.
  awp_apply (thread_update_state with "HInv").
  iApply (aacc_aupd_commit with "AU"); first done.
  iIntros "H".
  iAaccIntro with "H"; first by iIntros "$ !> AU".
  by iIntros "$ !> $ !>".
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

Inductive inhabitedCellTerminalState :=
| cellCancelled
| cellResumed
| cellAbandoned.

Inductive cellState :=
| cellFilled
| cellInhabited : gname -> loc -> option inhabitedCellTerminalState -> cellState.

Notation cellProgressUR := mnatUR (only parsing).
Notation cellUninitializedO := (0%nat: mnatUR) (only parsing).
Notation cellInitializedO := (1%nat: mnatUR) (only parsing).
Notation cellInhabitedO := (2%nat: mnatUR) (only parsing).
Notation cellDoneO := (3%nat: mnatUR) (only parsing).

Canonical Structure cellTerminalStateO := leibnizO cellState.

Notation cellInhabitantPassR := (optionUR fracR).
Notation cellInhabitantThreadR := (optionUR (agreeR (prodO gnameO locO))).
Notation cellInhabitantUR := (prodUR cellInhabitantPassR cellInhabitantThreadR).

Notation cellResumerPassUR := (optionUR (exclR unitO)).
Notation cellResumerUR := cellResumerPassUR.

Notation cellTerminalStateUR := (optionUR (agreeR cellTerminalStateO)).

Notation cellStateUR := (prodUR (prodUR (prodUR cellInhabitantUR cellResumerUR)
                                        cellProgressUR)
                                cellTerminalStateUR).

Notation queueContentsUR := (listUR cellStateUR).

Notation enqueueUR := natUR.
Notation dequeueUR := (prodUR natUR mnatUR).
Notation algebra := (authUR (prodUR (prodUR enqueueUR dequeueUR) queueContentsUR)).

Class threadQueueG Σ := ThreadQueueG { thread_queue_inG :> inG Σ algebra }.
Definition threadQueueΣ : gFunctors := #[GFunctor algebra].
Instance subG_threadQueueΣ {Σ} : subG threadQueueΣ Σ -> threadQueueG Σ.
Proof. solve_inG. Qed.

Context `{heapG Σ} `{iArrayG Σ} `{iteratorG Σ} `{threadQueueG Σ} `{parkingG Σ}.
Variable (N: namespace).
Variable (Nth: namespace).
Notation iProp := (iProp Σ).

Variable segment_size: positive.

Definition rendezvous_state γtq i (r: cellStateUR) :=
  own γtq (◯ (ε, {[ i := r ]})).

Lemma rendezvous_state_op γtq i (r r': cellStateUR):
  (rendezvous_state γtq i r ∗ rendezvous_state γtq i r' ⊣⊢
   rendezvous_state γtq i (r ⋅ r'))%I.
Proof.
  rewrite /rendezvous_state -own_op -auth_frag_op -pair_op ucmra_unit_left_id.
  by rewrite list_op_singletonM.
Qed.

Global Instance rendezvous_state_persistent γtq i (r: cellStateUR):
  CoreId r -> Persistent (rendezvous_state γtq i r).
Proof. apply _. Qed.

Definition rendezvous_done γtq i (c: cellState) :=
  rendezvous_state γtq i ((ε, cellDoneO), Some (to_agree c)).

Global Instance rendezvous_done_persistent γtq i c :
  Persistent (rendezvous_done γtq i c).
Proof. apply _. Qed.

Definition rendezvous_resumed (γtq: gname) (i: nat): iProp :=
  (∃ γ ℓ, rendezvous_done γtq i (cellInhabited γ ℓ (Some cellResumed)))%I.
Definition rendezvous_filled (γtq: gname) (i: nat): iProp :=
  rendezvous_done γtq i cellFilled.
Definition rendezvous_cancelled (γtq: gname) (i: nat): iProp :=
  (∃ γ ℓ, rendezvous_done γtq i (cellInhabited γ ℓ (Some cellCancelled)))%I.
Definition rendezvous_abandoned (γtq: gname) (i: nat): iProp :=
  (∃ γ ℓ, rendezvous_done γtq i (cellInhabited γ ℓ (Some cellAbandoned)))%I.
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

Definition tq_ap (γtq γd: gname) :=
  {|
    p_cell_is_done_persistent := iterator_counter_at_least_persistent γd;
    p_cell_invariant_persistent := cell_invariant_persistent γtq;
  |}.

Theorem tq_cell_init γtq γd:
  cell_init segment_size (tq_ap γtq γd) ∅.
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
               (count_matching P l + (to_num (f v)) - (to_num v))%nat.
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

Definition cellStateProgress (k: option cellState): cellProgressUR :=
  match k with
  | None => cellUninitializedO
  | Some cellFilled => cellDoneO
  | Some (cellInhabited _ _ None) => cellInhabitedO
  | Some (cellInhabited _ _ (Some _)) => cellDoneO
  end.

(* The cell is still present in the queue. *)
Definition still_present (k: option cellState): bool :=
  match k with
  | Some cellFilled => false
  | Some (cellInhabited _ _ (Some _)) => false
  | _ => true
  end.

Definition cell_state_to_RA (k: option cellState): cellStateUR :=
  match k with
    | None => (ε, cellUninitializedO, None)
    | Some cellFilled => (ε, cellDoneO, Some (to_agree cellFilled))
    | Some (cellInhabited γ ℓ s) =>
      match s with
        | None => (Some 1%Qp, Some (to_agree (γ, ℓ)), None, cellInhabitedO, None)
        | Some d =>
          (Some 1%Qp,
           Some (to_agree (γ, ℓ)),
           match d with
           | cellResumed => Excl' ()
           | cellCancelled => Excl' ()
           | _ => None
           end,
           cellDoneO,
           Some (to_agree (cellInhabited γ ℓ s)))
      end
  end.

Definition inhabitant_token' γtq i q :=
  rendezvous_state γtq i (Some q, ε, ε, ε, ε).

Definition inhabitant_token γtq i :=
  inhabitant_token' γtq i 1%Qp.

Lemma pair_op_1 {A: ucmraT} {B: cmraT} (b b': B):
  (b ⋅ b', ε) ≡ (b, (ε: A)) ⋅ (b', (ε: A)).
Proof. by rewrite -pair_op ucmra_unit_left_id. Qed.

Lemma inhabitant_token_exclusive γtq i q:
  inhabitant_token γtq i -∗ inhabitant_token' γtq i q -∗ False.
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
  rewrite minus_diag. simpl. rewrite list_lookup_singletonM.
  rewrite -Some_op Some_valid.
  move=> HValid.
  repeat (apply pair_valid in HValid; destruct HValid as [HValid _]).
  move: HValid. simpl. rewrite -Some_op Some_valid.
  rewrite frac_valid'.
  move=> HValid. by apply Qp_not_plus_q_ge_1 in HValid.
Qed.

Definition deq_front_at_least γtq (n: nat) :=
  own γtq (◯ (ε, (ε, n: mnatUR), ε)).

Definition rendezvous_thread_locs_state (γtq γt: gname) (th: loc) (i: nat): iProp
  := rendezvous_state γtq i (ε, Some (to_agree (γt, th)), ε, ε, ε).

Global Instance rendezvous_thread_locs_state_persistent γtq γt th i:
  Persistent (rendezvous_thread_locs_state γtq γt th i).
Proof.
  apply rendezvous_state_persistent.
  repeat apply pair_core_id.
  all: apply _.
Qed.

Definition rendezvous_thread_handle (γtq γt: gname) (th: loc) (i: nat): iProp :=
  (is_thread_handle Nth γt #th ∗
   rendezvous_thread_locs_state γtq γt th i)%I.

Global Instance rendezvous_thread_handle_persistent γtq γt th i:
  Persistent (rendezvous_thread_handle γtq γt th i).
Proof. apply _. Qed.

Definition resumer_token γtq i :=
  rendezvous_state γtq i (ε, ε, Excl' (), ε, ε).

Definition awakening_permit γtq := own γtq (◯ (ε, (1%nat, ε), ε)).

Definition canceller_token γtq i :=
  inhabitant_token' γtq i (1/2)%Qp.

Definition cell_resources E R γtq γa γe γd i k :=
  (match k with
   | None => True
   | Some cellState => ∃ ℓ, array_mapsto segment_size γa i ℓ ∗
        match cellState with
        | cellFilled => iterator_issued γd i ∗
                       cell_cancellation_handle segment_size γa i ∗
                       (iterator_issued γe i ∨ ℓ ↦ RESUMEDV ∗ R)
        | cellInhabited γt th None => (ℓ ↦ InjLV #th ∗
                                      thread_doesnt_have_permits γt ∗
                                      rendezvous_thread_handle γtq γt th i)
                                     ∗ iterator_issued γe i
                                     ∗ cell_cancellation_handle segment_size γa i
        | cellInhabited γt th (Some cd) => rendezvous_thread_handle γtq γt th i ∗
          iterator_issued γe i ∗
          match cd with
          | cellAbandoned => cell_cancellation_handle segment_size γa i ∗
                            inhabitant_token γtq i ∗
                            deq_front_at_least γtq (S i) ∗
                            (iterator_issued γd i ∨
                             E ∗ (ℓ ↦ InjLV #th ∗ thread_doesnt_have_permits γt))
          | cellCancelled => inhabitant_token' γtq i (1/2)%Qp ∗
                            (* Possibility 1: the cell is cancelled, but it
                               wasn't yet represented at all in the state of the
                               cell. In this case, the inhabitant receives the
                               `canceller_token` that establishes its right to
                               set `ℓ ↦ CANCELLEDV`, and the right for waking the
                               thread up is allocated and stored. Also, the cell
                               can't be cancelled without setting `ℓ ↦
                               CANCELLEDV`, so we also store
                               `cell_cancellation_handle`. Lastly, the thread has
                               no right to wake up, and because we may only ever
                               logically remove a cell in case there are some
                               cells left in the queue, we have the
                               awakening permit for the resumer (if the
                               physical cancellation is successful) or for
                               the inhabitant (if the resumer manages to set a
                               cancelled cell).
                             *)
                            (ℓ ↦ InjLV #th ∗ resumer_token γtq i ∗ E ∗
                             cell_cancellation_handle segment_size γa i ∗
                             thread_doesnt_have_permits γt ∗
                             awakening_permit γtq  ∨

                             ℓ ↦ RESUMEDV ∗ iterator_issued γd i ∗
                            (* Possibility 2: first, the cell was cancelled, then
                               it was marked with `CANCELLEDV`, and then with
                               `RESUMEDV`. In this case, the inhabitant can claim
                               the `cell_cancellation_handler` that was stored
                               here before; the resumer doesn't try to wake up
                               the cell, so it doesn't take the token, but
                               instead gets the awakening permit and proceeds to
                               wake up the next cell in line. *)
                               (canceller_token γtq i ∗
                                resumer_token γtq i ∨
                            (* Possibility 3: the cell was cancelled, then
                               marked with `RESUMEDV`, and the inhabitant hasn't
                               yet managed to write `CANCELLEDV`. In this case,
                               the resumer believes that it successfully resumed
                               a cell and now proceeds to awaken it, using the
                               `resumer_token`. By this point, nobody needs to
                               know -- or can guess -- whether a thread is
                               awoken or not, so the resumer just takes
                               `thread_doesnt_have_permits` with it. Also, when
                               the inhabitant does try to set `CANCELLEDV`, it
                               will learn that it lost the race and use the
                               `awakening_permit` stored here to wake up another
                               thread.
                             *)
                               cell_cancellation_handle segment_size γa i ∗
                               awakening_permit γtq) ∨

                             ℓ ↦ CANCELLEDV ∗ canceller_token γtq i ∗
                             (* Possibility 4: the cell was cancelled, then
                                `RESUMEDV`'d, and then `CANCELLEDV`'d. In this
                                case, the resumer has already taken the
                                `resumer_token` with it, leaving
                                `iterator_issued` behind, and the inhabitant
                                took `awakening_permit` and went on to wake up
                                another thread.
                              *)
                               (iterator_issued γd i ∗
                                cell_cancellation_handle segment_size γa i ∨
                              (* Possibility 5: the cell was cancelled, then
                                `CANCELLEDV`'d. Then the inhabitant took the
                                cancellation handler to physically cancel the
                                cell and left an `awakening_permit` for the
                                eventual resumer.
                               *)
                                resumer_token γtq i ∗
                                (awakening_permit γtq ∨
                                 iterator_issued γd i ∗
                                 cell_is_cancelled segment_size γa i)
                               )
                            )
                            (*
                            (awakening_permit γtq ∨ iterator_issued γd i) ∗
                            (ℓ ↦ CANCELLEDV ∨ ℓ ↦ RESUMEDV)
                            *)
          | cellResumed => iterator_issued γd i ∗
                          cell_cancellation_handle segment_size γa i ∗
                          (inhabitant_token γtq i ∗
                                            (thread_doesnt_have_permits γt ∨
                                             resumer_token γtq i) ∨
                           ℓ ↦ RESUMEDV ∗ R ∗ (thread_has_permit γt ∗
                                                 resumer_token γtq i ∨
                                                 thread_doesnt_have_permits γt))
          end
        end
  end)%I.

Definition option_Pos_of_nat (n: nat): option positive :=
  match n with
  | O => None
  | S n' => Some (Pos.of_nat n)
  end.

Definition cell_list_contents_auth_ra l (deqFront: nat) :=
  (length l, ((deqFront + count_matching (fun b => not (still_present b)) (drop deqFront l))%nat,
              deqFront: mnatUR), map cell_state_to_RA l).

Lemma included_None {A: cmraT} (a : option A):
  (a ≼ None) -> a = None.
Proof.
  rewrite option_included. case; first done.
  intros (? & ? & _ & HContra & _). discriminate.
Qed.

Lemma list_lookup_singletonM_lt:
    forall (A: ucmraT) (i i': nat) (x: A),
                (i' < i)%nat -> list_singletonM i x !! i' = Some (ε: A).
Proof.
  induction i; intros [|i']; naive_solver auto with lia.
Qed.

Lemma list_lookup_singletonM_gt:
    forall (A: ucmraT) (i i': nat) (x: A),
                (i < i')%nat -> list_singletonM i x !! i' = None.
Proof.
  induction i; intros [|i']; naive_solver auto with lia.
Qed.

Lemma None_least (A: cmraT) (a: option A): None ≼ a.
Proof. by apply option_included; left. Qed.

Lemma list_singletonM_included {A: ucmraT} (i: nat) (x: A) (l: list A):
  {[i := x]} ≼ l <-> (exists v, l !! i = Some v ∧ x ≼ v).
Proof.
  rewrite list_lookup_included.
  split.
  {
    intros HEv. specialize (HEv i). move: HEv.
    rewrite list_lookup_singletonM. destruct (l !! i) as [x'|].
    2: by intros HContra; apply included_None in HContra.
    rewrite Some_included_total. eauto.
  }
  {
    intros (v & HEl & HInc) i'.
    destruct (decide (i < i')%nat).
    {
      rewrite list_lookup_singletonM_gt //.
      apply None_least.
    }
    destruct (decide (i = i')%nat).
    {
      subst.
      rewrite list_lookup_singletonM. rewrite HEl.
      by apply Some_included_total.
    }
    {
      rewrite list_lookup_singletonM_lt; last lia.
      assert (i < length l)%nat.
      by apply lookup_lt_is_Some; eauto.
      assert (is_Some (l !! i')) as [? HEl'].
      by apply lookup_lt_is_Some; lia.
      rewrite HEl' Some_included_total.
      apply ucmra_unit_least.
    }
  }
Qed.

Theorem cell_list_contents_done_agree γ l (deqFront: nat) i c:
  own γ (● (cell_list_contents_auth_ra l deqFront)) -∗
  rendezvous_done γ i c -∗
  ⌜l !! i ≡ Some (Some c)⌝.
Proof.
  iIntros "HAuth HFrag".
  iDestruct (own_valid_2 with "HAuth HFrag")
    as %[[_ (v&HEl&HInc)%list_singletonM_included]%prod_included _]%auth_both_valid.
  simpl in *. iPureIntro.

  rewrite map_lookup in HEl.
  destruct (l !! i) as [el|]; simpl in *; inversion HEl; subst.
  clear HEl.
  apply prod_included in HInc.
  destruct el as [el'|]; simpl in *.
  2: {
    destruct HInc as [_ HInc].
    by apply included_None in HInc.
  }
  destruct el' as [|γ' ℓ d]; simpl in *.
  {
    destruct HInc as [_ HInc]. move: HInc.
    rewrite Some_included_total to_agree_included.
    by intros ->.
  }
  destruct d as [d|]; simpl in *.
  {
    destruct HInc as [_ HInc]. move: HInc.
    rewrite Some_included_total to_agree_included.
    by intros ->.
  }
  destruct HInc as [HInc _]. apply prod_included in HInc; simpl.
  destruct HInc as [_ HInc]. move: HInc. simpl.
  rewrite mnat_included. lia.
Qed.

Theorem cell_list_contents_ra_locs γ l deqFront i γt th:
  own γ (● (cell_list_contents_auth_ra l deqFront)) -∗
  rendezvous_thread_locs_state γ γt th i -∗
  ⌜exists c, l !! i ≡ Some (Some (cellInhabited γt th c))⌝.
Proof.
  iIntros "HAuth HFrag".
  iDestruct (own_valid_2 with "HAuth HFrag")
    as %[[_ (v&HEl&HInc)%list_singletonM_included]%prod_included _]%auth_both_valid.
  simpl in *. iPureIntro.

  rewrite map_lookup in HEl.
  destruct (l !! i) as [el|]; simpl in *; inversion HEl; subst.
  clear HEl.

  apply prod_included in HInc; simpl in *. destruct HInc as [HInc _].
  apply prod_included in HInc; simpl in *. destruct HInc as [HInc _].
  apply prod_included in HInc; simpl in *. destruct HInc as [HInc _].
  apply prod_included in HInc; simpl in *. destruct HInc as [_ HInc].

  destruct el as [el'|]; simpl in *.
  2: by apply included_None in HInc.
  destruct el' as [|γ' ℓ d]; simpl in *.
  by apply included_None in HInc.
  move: HInc.
  destruct d as [d|]; simpl in *; rewrite Some_included_total to_agree_included.
  all: intros; simplify_eq; eauto.
Qed.

(* The resumer hasn't been assigned yet *)
Definition resumer_stage_0 (o: option cellState): bool :=
  match o with
  | Some cellFilled => false
  | Some (cellInhabited _ _ (Some cellResumed)) => false
  | Some (cellInhabited _ _ (Some cellAbandoned)) => false
  | _ => true
  end.

Definition cell_list_contents (S R: iProp) γa γtq γe γd
           (l: list (option cellState)) (deqFront: nat): iProp :=
  (let nEnq := count_matching still_present l in
   let nDeq := count_matching still_present (take deqFront l) in
   ⌜deqFront <= length l⌝ ∗
   ([∗ list] x ∈ drop deqFront l, ⌜resumer_stage_0 x = true⌝) ∗
   own γtq (● cell_list_contents_auth_ra l deqFront) ∗
       ([∗ list] s ∈ replicate nEnq S, s) ∗ ([∗ list] r ∈ replicate nDeq R, r) ∗
       ([∗ list] i ↦ k ∈ l, cell_resources S R γtq γa γe γd i k))%I.

Definition suspension_permit γtq := own γtq (◯ (1%nat, ε, ε)).

Definition exists_list_element γtq (n: nat) :=
  own γtq (◯ (ε, {[ n := ε ]})).

Theorem exists_list_element_lookup γtq l i d:
  exists_list_element γtq i -∗
  own γtq (● (cell_list_contents_auth_ra l d)) -∗
  ⌜exists v, l !! i = Some v⌝.
Proof.
  iIntros "HExistsEl HAuth".
  iDestruct (own_valid_2 with "HAuth HExistsEl")
    as %[[_ HH]%prod_included _]%auth_both_valid.
  simpl in *. iPureIntro.
  apply list_singletonM_included in HH.
  destruct HH as (v & HMap & _). rewrite map_lookup in HMap.
  destruct (l !! i); simpl in *; [eauto|done].
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

Fixpoint find_index {A} (P: A -> Prop) {H': forall x, Decision (P x)}
         (l: list A): option nat :=
  match l with
  | nil => None
  | cons x l => if decide (P x) then Some 0%nat
               else option_map S (find_index P l)
  end.

Lemma find_index_Some {A} (P: A -> Prop) {H': forall x, Decision (P x)}:
  forall l i, find_index P l = Some i ->
         (exists v, l !! i = Some v /\ P v) /\
         (forall i', (i' < i)%nat -> exists v', l !! i' = Some v' /\ not (P v')).
Proof.
  induction l; first done; simpl in *.
  case; simpl; destruct (decide (P a)).
  by intros _; split; [eauto|intros i; lia].
  by destruct (find_index P l).
  done.
  destruct (find_index P l); try done.
  simpl in *.
  intros n' ?; simplify_eq.
  destruct (IHl _ eq_refl) as [HEl HRst].
  split; first done.
  case; simpl; first by eauto.
  intros. apply HRst. lia.
Qed.

Lemma find_index_None {A} (P: A -> Prop) {H': forall x, Decision (P x)}:
  forall l, find_index P l = None -> forall v, In v l -> not (P v).
Proof.
  induction l; simpl; first done.
  destruct (decide (P a)); first done.
  destruct (find_index P l); first done.
  intros _ ? HEv; subst.
  inversion HEv; subst; eauto.
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

Global Instance deq_front_at_least_persistent γtq n:
  Persistent (deq_front_at_least γtq n).
Proof.
  apply own_core_persistent, auth_frag_core_id, pair_core_id; apply _.
Qed.

Theorem prod_included':
  forall (A B: cmraT) (x y: (A * B)), x.1 ≼ y.1 ∧ x.2 ≼ y.2 -> x ≼ y.
Proof.
    by intros; apply prod_included.
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

Theorem cell_list_contents__deq_front_at_least i γtq l deqFront:
  (i <= deqFront)%nat ->
  own γtq (● cell_list_contents_auth_ra l deqFront) ==∗
  own γtq (● cell_list_contents_auth_ra l deqFront) ∗
  deq_front_at_least γtq i.
Proof.
  iIntros (HLe) "HAuth".
  iMod (own_update with "HAuth") as "[$ $]"; last done.
  apply auth_update_core_id.
  by repeat apply pair_core_id; apply _.
  repeat (apply prod_included'; split); simpl.
  all: try apply ucmra_unit_least.
  apply mnat_included. lia.
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

Lemma present_cells_in_take_i_if_next_present_is_Si
  {A: Type} (P: A -> Prop) {H': forall x, Decision (P x)} (i: nat) (l: list A):
    find_index P l = Some i ->
    count_matching P (take i l) = O.
Proof.
  intros HFindSome.
  apply find_index_Some in HFindSome.
  destruct HFindSome as [[v [HIn HPresent]] HNotPresent].
  assert (i < length l)%nat as HLt.
  { apply lookup_lt_is_Some. by eexists. }

  assert (forall i', (i' < i)%nat -> exists v', take i l !! i' = Some v' /\
                                      not (P v')) as HH.
  {
    intros i' HLti'. destruct (HNotPresent i' HLti')
      as [v' [HEl Hv'NotPresent]].
    exists v'. split; try done. by rewrite lookup_take.
  }
  remember (take i l) as l'. assert (i = length l') as HLen.
  by subst; rewrite take_length_le; lia.
  subst i.
  revert HH. clear. rewrite /count_matching /filter /=.
  induction l'; auto=> H. simpl in *.
  destruct (H O) as [p H'']; simpl in *; first by lia.
  destruct H'' as [[=] HH]; subst. destruct (decide (P p)).

  contradiction.
  apply IHl'.
  intros i' HLt.
  destruct (H (S i')); first by lia.
  simpl in *. eauto.
Qed.

Lemma present_cells_in_take_1_drop_i_if_next_present_is_Si
  {A: Type} (P: A -> Prop) {H': forall x, Decision (P x)} (i: nat) (l: list A):
    find_index P l = Some i ->
    count_matching P (take 1 (drop i l)) = 1%nat.
Proof.
  intros HFindSome.
  apply find_index_Some in HFindSome.
  destruct HFindSome as [[v [HIn HPresent]] HNotPresent].
  assert (i < length l)%nat as HLt.
  { apply lookup_lt_is_Some. by eexists. }

  replace (drop i l) with (v :: drop (S i) l).
  { simpl. destruct (decide (P v)); try contradiction. done. }
  assert (i = length (take i l))%nat as HH.
  by rewrite take_length_le; lia.
  replace (drop i l) with (drop i (take i l ++ v :: drop (S i) l)).
  { symmetry. rewrite drop_app_le. rewrite drop_ge. done. all: lia. }
  by rewrite take_drop_middle.
Qed.

Lemma present_cells_in_take_Si_if_next_present_is_Si
  {A: Type} (P: A -> Prop) {H': forall x, Decision (P x)} (i: nat) (l: list A):
    find_index P l = Some i ->
    count_matching P (take (S i) l) = 1%nat.
Proof.
  intros HFindSome.
  change (S i) with (1 + i)%nat.
  rewrite Nat.add_comm -take_take_drop count_matching_app.
  rewrite present_cells_in_take_1_drop_i_if_next_present_is_Si.
  rewrite present_cells_in_take_i_if_next_present_is_Si.
  all: try done.
Qed.

Lemma absent_cells_in_drop_Si_if_next_present_is_i
  {A: Type} (P: A -> Prop) {H': forall x, Decision (P x)} (i: nat) (l: list A):
    find_index P l = Some i ->
  count_matching (λ b, not (P b)) l =
  (i + count_matching (λ b, not (P b)) (drop (S i) l))%nat.
Proof.
  intros HFindSome.
  repeat rewrite count_matching_complement.
  rewrite drop_length.

  replace (count_matching P l) with
      (count_matching P (take (S i) l ++ drop (S i) l)).
  2: by rewrite take_drop.

  rewrite count_matching_app Nat.sub_add_distr.
  rewrite present_cells_in_take_Si_if_next_present_is_Si; try done.

  repeat rewrite -Nat.sub_add_distr /=.
  remember (count_matching (_) (drop (S i) _)) as K.
  rewrite plus_n_Sm.
  rewrite -(Nat.add_comm (S K)) Nat.sub_add_distr.
  assert (K <= length l - S i)%nat as HKLt.
  {
    rewrite HeqK. eapply transitivity.
    apply count_matching_le_length.
    by rewrite drop_length.
  }
  assert (i < length l)%nat; try lia.
  apply find_index_Some in HFindSome.
  destruct HFindSome as [(v & HEl & _) _].
  apply lookup_lt_is_Some. eauto.
Qed.

Lemma deque_register_ra_update l deqFront:
  forall i, find_index still_present (drop deqFront l) = Some i ->
  ● cell_list_contents_auth_ra l deqFront ~~>
    ● cell_list_contents_auth_ra l (deqFront + S i)
    ⋅ (◯ (ε, (1%nat, ε), ε) ⋅ ◯ (ε, (ε, (deqFront + S i)%nat : mnatUR), ε)).
Proof.
  intros i HFindSome.

  assert (deqFront + i < length l)%nat.
  {
    apply find_index_Some in HFindSome.
    destruct HFindSome as [[v [HIn HPresent]] HNotPresent].
    assert (i < length (drop deqFront l))%nat as HLt.
    { apply lookup_lt_is_Some. by eexists. }
    rewrite drop_length in HLt. lia.
  }

  rewrite -auth_frag_op.
  repeat rewrite -pair_op ucmra_unit_left_id. rewrite ucmra_unit_right_id.

  apply auth_update_alloc, prod_local_update_1, prod_local_update_2,
    prod_local_update'.
  2: apply mnat_local_update; lia.
  apply nat_local_update.

  rewrite -plus_n_O -Nat.add_assoc Nat.add_1_r -Nat.add_assoc /=.
  congr (fun x => deqFront + (S x))%nat.
  rewrite -drop_drop.

  by rewrite -absent_cells_in_drop_Si_if_next_present_is_i.
Qed.

Theorem cell_list_contents_register_for_dequeue E R γa γtq γe γd l deqFront:
  forall i, find_index still_present (drop deqFront l) = Some i ->
  R -∗ cell_list_contents E R γa γtq γe γd l deqFront ==∗
  (awakening_permit γtq ∗ deq_front_at_least γtq (deqFront + S i)%nat) ∗
  cell_list_contents E R γa γtq γe γd l (deqFront + S i)%nat ∗
  ⌜count_matching still_present (drop deqFront l) =
   S (count_matching still_present (drop (deqFront + S i) l))⌝.
Proof.
  iIntros (i HFindSome).

  assert (count_matching still_present (take i (drop deqFront l)) = O)
    as HCountMatching2.
  by apply present_cells_in_take_i_if_next_present_is_Si.

  assert (count_matching still_present (take 1 (drop i (drop deqFront l))) = 1%nat)
    as HCountMatching3.
  by apply present_cells_in_take_1_drop_i_if_next_present_is_Si.

  assert (S (count_matching still_present (take deqFront l)) =
              count_matching still_present (take (deqFront + S i) l)) as HCountMatching.
  {
    rewrite -take_take_drop.
    assert (take i (drop deqFront l) ++ take 1 (drop i (drop deqFront l)) =
            take (S i) (drop deqFront l)) as <-.
    by rewrite take_take_drop Nat.add_comm.
    repeat rewrite count_matching_app.
    rewrite present_cells_in_take_1_drop_i_if_next_present_is_Si.
    rewrite (present_cells_in_take_i_if_next_present_is_Si _ i).
    lia.
    all: done.
  }

  assert (count_matching still_present (drop deqFront l) > 0)%nat as HCM4.
  {
    apply find_index_Some in HFindSome.
    destruct HFindSome as [[v [HIn HPresent]] HNotPresent].
    replace (drop deqFront l) with
        (take i (drop deqFront l) ++ v :: drop (S i) (drop deqFront l)).
    2: by apply take_drop_middle.
    rewrite count_matching_app. simpl.
    rewrite decide_left.
    lia.
  }

  assert (deqFront + i < length l)%nat.
  {
    apply find_index_Some in HFindSome.
    destruct HFindSome as [[v [HIn HPresent]] HNotPresent].
    assert (i < length (drop deqFront l))%nat as HLt.
    { apply lookup_lt_is_Some. by eexists. }
    rewrite drop_length in HLt. lia.
  }

  iIntros "HR (% & #HNotDone & HAuth & HSs & HRs & HCellResources)".

  iMod (own_update with "HAuth") as "[HAuth [HFrag1 HFrag2]]".
  by apply deque_register_ra_update.
  iFrame "HFrag1 HFrag2". iSplitL.
  2: {
    iPureIntro.
    rewrite count_matching_drop count_matching_drop.
    rewrite -HCountMatching.
    remember (count_matching _ l) as K.
    remember (count_matching _ (take deqFront l)) as K'.
    assert (K - K' > 0)%nat.
    2: lia.
    subst.
    by rewrite -count_matching_drop.
  }
  iSplitR.
  by iPureIntro; lia.
  iFrame. rewrite -HCountMatching. simpl. iFrame.
  repeat rewrite big_sepL_forall.
  iIntros "!>" (k ? HEv). iApply ("HNotDone" $! (k + S i)%nat).
  iPureIntro. rewrite <- HEv.
  repeat rewrite lookup_drop. congr (fun x => l !! x). lia.
Qed.

Definition is_thread_queue (S R: iProp) γa γtq γe γd eℓ epℓ dℓ dpℓ l deqFront :=
  let ap := tq_ap γtq γd in
  (is_infinite_array segment_size ap γa ∗
   cell_list_contents S R γa γtq γe γd l deqFront ∗
   ⌜(deqFront > 0 /\ ∃ γt th,
        l !! (deqFront - 1)%nat =
        Some (Some (cellInhabited γt th (Some cellCancelled)))) -> False⌝ ∧
   ∃ (enqIdx deqIdx: nat),
   iterator_points_to segment_size γa γe eℓ epℓ enqIdx ∗
   iterator_points_to segment_size γa γd dℓ dpℓ deqIdx ∗
   ([∗ list] i ∈ seq 0 deqIdx, awakening_permit γtq) ∗
   ([∗ list] i ∈ seq 0 enqIdx, suspension_permit γtq) ∗
   ⌜deqIdx <= deqFront <= length l⌝ ∧ ⌜enqIdx <= length l⌝
  )%I.

Theorem thread_queue_append E R γa γtq γe γd l deqFront eℓ epℓ dℓ dpℓ:
  E -∗ is_thread_queue E R γa γtq γe γd eℓ epℓ dℓ dpℓ l deqFront ==∗
  (suspension_permit γtq ∗
  exists_list_element γtq (length l)) ∗
  is_thread_queue E R γa γtq γe γd eℓ epℓ dℓ dpℓ (l ++ [None]) deqFront.
Proof.
  iIntros "HE (HInfArr & HListContents & HDeqIdx & HIts)".
  iMod (cell_list_contents_append with "HE HListContents") as "($ & $ & $)".
  iFrame "HInfArr"; simpl.
  iDestruct "HDeqIdx" as %HDeqIdx.
  iDestruct "HIts" as (enqIdx deqIdx) "(HEnqIt & HDeqIt & HAwaks & HSusps & %)".
  iSplitR.
  {
    iPureIntro.
    destruct deqFront; first lia.
    rewrite lookup_app_l; first done.
    lia.
  }
  iExists enqIdx, deqIdx. iFrame.
  iPureIntro. rewrite app_length.
  lia.
Qed.

Lemma awakening_permit_implies_bound i (E R: iProp) γtq γa γd γe dℓ l deqFront deqIdx:
  ⌜(deqIdx <= deqFront)%nat⌝ -∗
  ([∗ list] i ∈ seq 0 i, awakening_permit γtq) -∗
  iterator_counter γd dℓ deqIdx -∗
   ([∗ list] i ∈ seq 0 deqIdx, awakening_permit γtq) -∗
  cell_list_contents E R γa γtq γe γd l deqFront -∗
   ⌜deqIdx + i <= deqFront⌝.
Proof.
  iIntros (HLt) "HCAwaks HCounter HDeqAwaks HCellResources".
  iDestruct "HCellResources" as "(% & #HNotDone & HAuth & _ & _ & HRRs)".
  replace l with (take deqFront l ++ drop deqFront l).
  2: by rewrite take_drop.
  repeat rewrite big_sepL_app.
  iDestruct "HRRs" as "[_ HRRs]".
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
                exists v, l !! j = Some v /\ resumer_stage_0 v = true⌝)%I with "[-]" as %HH.
  {
    rewrite big_sepL_forall. iIntros (j [HB1 HB2]).
    apply lookup_lt_is_Some_2 in HB2. destruct HB2 as [v HB2].
    iSpecialize ("HNotDone" $! (j-deqFront)%nat v).
    rewrite lookup_drop. replace (deqFront + (_ - _))%nat with j by lia.
    iDestruct ("HNotDone" with "[]") as "%"; first done.
    rewrite HB2.
    iExists _. eauto.
  }
  iAssert ([∗ list] k ↦ y ∈ drop deqFront l, if (decide (not (still_present y)))
                                             then
                                               awakening_permit γtq ∨
                                               (∃ k', iterator_issued γd (deqFront + k'))
                                             else True)%I
    with "[HRRs]" as "HAwak".
  {
    iDestruct (big_sepL_mono with "HRRs") as "$".
    iIntros (k v HEv) "HV".
    rewrite lookup_drop in HEv.
    destruct (HH (deqFront + k)%nat) as [? [HEq HSt]]; simplify_eq; simpl in *.
    { split; try lia. apply lookup_lt_is_Some. by eauto. }
    destruct v as [c|]; simpl in *; eauto.
    destruct c as [|? ? c]; simpl in *; try done.
    destruct c as [c|]; simpl in *; eauto.
    destruct c; simpl in *; inversion HSt; try done.
    iDestruct "HV" as (?) "(_ & _ & _ & _ & HH)".
    iDestruct "HH" as "[(_ & _ & _ & _ & _ & V)|[(_ & V & _)|(_ & _ & [(V & _)|
      [_ [V|[V _]]]])]]"; eauto.
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

Lemma cell_list_contents_lookup_acc' i E R γa γtq γe γd l deqFront:
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

Lemma cell_list_contents_lookup_acc i E R γa γtq γe γd l deqFront c:
  l !! i = Some c ->
  cell_list_contents E R γa γtq γe γd l deqFront -∗
  cell_resources E R γtq γa γe γd i c ∗
  (cell_resources E R γtq γa γe γd i c -∗
   cell_list_contents E R γa γtq γe γd l deqFront).
Proof.
  iIntros (HEl).
  replace c with (mjoin (l !! i)).
  2: by rewrite HEl.
  iApply cell_list_contents_lookup_acc'.
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
  destruct c as [|? ? c].
  - iDestruct "HR" as "(_ & HR & _)".
    by iDestruct (cell_cancellation_handle'_exclusive with "HR HCancHandle") as %[].
  - destruct c as [c|].
    2: {
      iDestruct "HR" as "[[HR _] _]".
      iApply "HContra"; by eauto.
    }
    destruct c.
    * iDestruct "HR" as "(_ & _ & _ & [[HPtr' _]|[[HPtr' _]|[HPtr' _]]])".
      all: by iApply "HContra"; eauto.
    * iDestruct "HR" as "(_ & _ & _ & HCancHandle' & _)".
      iApply (cell_cancellation_handle'_exclusive with "HCancHandle HCancHandle'").
    * iDestruct "HR" as "(_ & _ & HCancHandle' & _)".
      iApply (cell_cancellation_handle'_exclusive with "HCancHandle HCancHandle'").
Qed.

Lemma enquirer_not_present_means_filled_if_initialized
      E R γtq γa γe γd i c l d:
  l !! i = Some c ->
  cell_resources E R γtq γa γe γd i c -∗
  own γtq (● cell_list_contents_auth_ra l d) -∗
  rendezvous_initialized γtq i -∗
  iterator_issued γe i -∗
  ⌜c = Some cellFilled⌝.
Proof.
  iIntros (HIsSome) "HCellRes HAuth HCellInit HIsSus".
  destruct c as [c|].
  2: {
    iDestruct (own_valid_2 with "HAuth HCellInit") as
        %[[_ HContra]%prod_included _]%auth_both_valid.
    exfalso.
    move: HContra. rewrite list_lookup_included.
    intros HContra. specialize (HContra i). simpl in *.
    revert HContra.
    revert HIsSome. clear. revert i. induction l. done.
    case; simpl in *; last assumption.
    intros HH. simplify_eq.
    rewrite /= Some_included_total.
    intros HContra. apply prod_included in HContra. simpl in *.
    case HContra.
    intros HContra' _. apply prod_included in HContra'. simpl in *.
    case HContra'.
    rewrite mnat_included; lia.
  }
  destruct c as [|? ? c]; simpl; first done.
  iExFalso.
  iDestruct "HCellRes" as (?) "[HArrMapsto HCellRes]".
  destruct c as [c|].
  2: {
    iDestruct "HCellRes" as "(_ & HIsSus' & _)".
    iDestruct (iterator_issued_exclusive with "HIsSus HIsSus'") as %[].
  }
  iDestruct "HCellRes" as "[_ HCellRes]".
  destruct c; simpl.
  all: iDestruct "HCellRes" as "(HIsSus' & _)".
  all: iDestruct (iterator_issued_exclusive with "HIsSus HIsSus'") as %[].
Qed.

Lemma None_op_left_id {A: cmraT} (a: option A): None ⋅ a = a.
Proof. rewrite /op /cmra_op /=. by destruct a. Qed.

Theorem prod_included'':
  forall (A B: cmraT) (x y: (A * B)), x ≼ y -> x.1 ≼ y.1 ∧ x.2 ≼ y.2.
Proof.
    by intros; apply prod_included.
Qed.

Theorem inhabit_cell_spec N' E R γa γtq γe γd γt i ptr (th: loc):
  is_thread_handle Nth γt #th -∗
  thread_doesnt_have_permits γt -∗
  iterator_issued γe i -∗
  exists_list_element γtq i -∗
  array_mapsto segment_size γa i ptr -∗
  inv N' (cell_invariant γtq γa i ptr) -∗
  <<< ∀ l deqFront, ▷ cell_list_contents E R γa γtq γe γd l deqFront >>>
    getAndSet #ptr (InjLV #th) @ ⊤ ∖ ↑N'
  <<< ∃ r, ⌜l !! i = Some None⌝ ∧
           ⌜r = InjLV #()⌝ ∧
           inhabitant_token γtq i ∗
           rendezvous_thread_handle γtq γt th i ∗
           ▷ cell_list_contents E R γa γtq γe γd
             (alter (fun _ => Some (cellInhabited γt th None)) i l) deqFront ∨
           ⌜l !! i = Some (Some cellFilled)⌝ ∧
           ⌜r = RESUMEDV⌝ ∧
           thread_doesnt_have_permits γt ∗
           ▷ R ∗
           ▷ cell_list_contents E R γa γtq γe γd l deqFront , RET r >>>.
Proof.
  iIntros "#HTh HThreadNoPerms HIsSus #HExistsEl #HArrMapsto #HCellInv" (Φ) "AU".
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
    iDestruct (big_sepL_lookup_alter i O
                (fun _ => Some (cellInhabited γt th None))) as "HH";
      first done.
    simpl; iSpecialize ("HH" with "HCellRRs").
    iDestruct "HH" as "[_ HH]".
    remember (alter (fun _ => Some (cellInhabited γt th None)) i l) as l'.
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
          ⋅ ◯ (ε, {[i := (Some 1%Qp, Some (to_agree (γt, th)), ε, 2%nat: mnatUR, None)]}
              ))
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
    iSpecialize ("HH" with "[HIsSus Hℓ HCancHandle HThreadNoPerms]").
    { iFrame. iExists _. iFrame "HArrMapsto Hℓ HRendThread HTh". }
    iAssert (own γtq (◯ (ε, {[i := (ε, 1%nat: mnatUR, None)]})))
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
      apply ucmra_unit_least. rewrite mnat_included. lia. }
    iFrame.

    iMod ("HClose" with "[-]") as "$".
    2: by iFrame "HInit".

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

    iAssert (▷ ⌜cr = Some cellFilled⌝)%I with "[-]" as "#>->".
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

Theorem prod_included''':
  forall (A B: cmraT) (x x' : A) (y y': B), (x, y) ≼ (x', y') -> x ≼ x' ∧ y ≼ y'.
Proof.
  intros ? ? ? ? ? ? HEv.
  apply prod_included'' in HEv.
  by simpl in *.
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
  iIntros "HInhToken (_ & _ & HAuth & _ & _ & HRRs)".
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

Lemma drop_alter' {A} (f: A -> A) n i (l: list A):
  drop n (alter f (n+i)%nat l) = alter f i (drop n l).
Proof.
  revert n.
  induction l; first by case.
  case; first done.
  auto.
Qed.

Lemma take_drop_middle_alter A (l: list A) (i: nat) f (x: A):
  l !! i = Some x ->
  alter f i l = take i l ++ (f x :: drop (S i) l).
Proof.
  intros HEl.
  assert (i < length l)%nat by (apply lookup_lt_is_Some; eauto).

  apply list_eq. intros j.
  destruct (decide (i = j)).
  {
    subst. rewrite list_lookup_alter HEl /=.
    rewrite lookup_app_r take_length_le; try lia.
    by rewrite minus_diag //.
  }
  {
    rewrite list_lookup_alter_ne //.
    destruct (decide (i < j)%nat).
    {
      rewrite lookup_app_r take_length_le; try lia.
      destruct (j - i)%nat eqn:E; first by lia.
      simpl.
      rewrite lookup_drop /= plus_n_Sm -E.
      replace (i + (j - i))%nat with j by lia.
      done.
    }
    {
      rewrite lookup_app_l. 2: rewrite take_length_le; try lia.
      rewrite lookup_take //. lia.
    }
  }
Qed.

Lemma cancel_rendezvous_spec E R γa γtq γe γd l deqFront i j:
  find_index still_present (drop deqFront l) = Some j ->
  inhabitant_token γtq i -∗
  ▷ cell_list_contents E R γa γtq γe γd l deqFront ==∗ ▷ (
  (∃ γt th, ⌜l !! i = Some (Some (cellInhabited γt th None))⌝ ∧
    cell_list_contents E R γa γtq γe γd
      (alter (fun _ => Some (cellInhabited γt th (Some cellCancelled))) i l)
      (if (decide (i < deqFront)%nat) then (deqFront + S j)%nat else deqFront) ∗
    canceller_token γtq i ∗
    rendezvous_cancelled γtq i ∨

    ⌜l !! i = Some (Some (cellInhabited γt th (Some cellResumed)))⌝ ∧
    cell_list_contents E R γa γtq γe γd l (deqFront + S j) ∗
    (∃ (ℓ: loc), array_mapsto segment_size γa i ℓ ∗ ▷ ℓ ↦ RESUMEDV) ∗
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
    iDestruct "HListContents" as "(_ & HL1 & >HAuth & HL2 & HL3 & HL4)".
    iMod (own_update with "HAuth") as "[HAuth [HFrag1 HFrag2]]".
    by apply deque_register_ra_update.

    iExists _, _. iRight. iFrame "HL2 HL4 HFrag1 HAuth".
    iSplitR; first done.
    iSplitR "Hℓ"; last by iExists _; iFrame.
    destruct (find_index_Some _ _ _ HFindIndex) as [(v & HElj & HPres) HOk].
    assert (deqFront + j < length l)%nat.
    { apply lookup_lt_is_Some. rewrite lookup_drop in HElj. eauto. }
    iSplitR; first by iPureIntro; lia.
    iSplitL "HL1".
    {
      rewrite -drop_drop. remember (drop deqFront l) as l'.
      replace l' with (take (S j) l' ++ drop (S j) l').
      2: by rewrite take_drop.
      rewrite big_sepL_app. rewrite take_drop. by iDestruct "HL1" as "[_ $]".
    }
    rewrite -take_take_drop count_matching_app replicate_plus big_sepL_app.
    iFrame "HL3".
    assert (count_matching still_present (take (S j) (drop deqFront l)) =
            1)%nat as ->; simpl.
    2: by iFrame.
    assert (take j (drop deqFront l) ++ take 1 (drop j (drop deqFront l)) =
            take (S j) (drop deqFront l)) as <-.
    by rewrite take_take_drop Nat.add_comm.
    rewrite count_matching_app.
    rewrite present_cells_in_take_1_drop_i_if_next_present_is_Si //.
    rewrite present_cells_in_take_i_if_next_present_is_Si //.
  }
  (* The cell was inhabited, but not resumed. Cancel it. *)
  iDestruct "HListContents" as
      "(>% & #>HResStage & >HAuth & HEs & HRs & HRRs)".

  assert (inhabitant_token γtq i ⊣⊢
          inhabitant_token' γtq i (1/2)%Qp ∗
          inhabitant_token' γtq i (1/2)%Qp)%I as Hsplit_inh_token.
  {
    rewrite -own_op -auth_frag_op -pair_op list_op_singletonM ucmra_unit_left_id.
    rewrite -pair_op ucmra_unit_right_id.
    replace (own γtq _) with (inhabitant_token γtq i). done.
    congr (own γtq (◯ (ε, {[ i := (Some _, ε, ε, ε, ε)]}))).
    symmetry. apply Qp_half_half.
  }

  assert ((map cell_state_to_RA l, ε) ~l~>
          (map cell_state_to_RA (alter (fun _ => Some (cellInhabited γt th (Some cellCancelled))) i l),
            {[ i := (ε, (cellDoneO: mnatUR),
                     Some (to_agree (cellInhabited γt th (Some cellCancelled))))]}
              ⋅ {[ i := (ε, Excl' (), ε, ε)]}
          )
          ) as Hupdate_ra_map.
  { move: HEl. clear. intros HInh.
    apply list_lookup_local_update.
    intros j. rewrite lookup_nil map_lookup map_lookup list_op_singletonM.
    destruct (decide (i = j)); first subst.
    {
      rewrite list_lookup_singletonM list_lookup_alter.
      rewrite HInh. simpl.
      apply option_local_update', prod_local_update; simpl.
      2: by apply alloc_option_local_update.
      apply prod_local_update; simpl.
      by apply prod_local_update_2, alloc_option_local_update.
      rewrite ucmra_unit_right_id.
      by apply mnat_local_update; lia.
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
      apply nat_local_update.
      by rewrite drop_alter; last lia.
    }
    iDestruct "HFrag" as "[HCanc HResTok]".

    rewrite Hsplit_inh_token alter_length.
    iDestruct "HInhToken" as "[$ HRRInh]".
    iSplitR "HCanc".
    2: by iExists _, _.
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
    repeat rewrite take_app_ge.
    all: try rewrite take_length_le.
    all: try lia.
    repeat rewrite count_matching_app.
    repeat rewrite replicate_plus.
    repeat rewrite big_sepL_app.
    iDestruct "HEs" as "($ & HE & $)".
    iDestruct "HRRs" as "($ & HRR & $)".
    destruct (deqFront - i)%nat eqn:HDec; first by lia.
    destruct (deqFront + S j - i)%nat eqn:HDec'; first by lia.
    simpl.
    iDestruct "HRs" as "($ & HR & HRs)".
    iSplitL "HR HRs".
    {
      repeat rewrite take_drop_commute /=.
      repeat rewrite plus_n_Sm.
      rewrite <- HDec. rewrite <- HDec'.
      replace (i + (deqFront - i))%nat with deqFront by lia.
      replace (i + (deqFront + S j - i))%nat with (deqFront + S j)%nat by lia.
      rewrite -take_take_drop drop_app_ge.
      2: rewrite take_length_le; by lia.
      rewrite drop_app_le.
      2: rewrite take_length_le; lia.
      rewrite count_matching_app replicate_plus big_sepL_app. iFrame "HRs".
      rewrite present_cells_in_take_Si_if_next_present_is_Si //.
      simpl. iFrame.
      done.
    }
    iDestruct "HRR" as (ℓ) "(HArrMapsto & (Hℓ & HNoPerms & HTh) & HIsSus & HCancHandle)".
    iExists ℓ.
    rewrite take_length_le; last lia. rewrite Nat.add_0_r.
    iFrame "HArrMapsto HTh HIsSus HRRInh".
    iLeft. by iFrame.
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
      apply (nat_local_update) with (y' := 1%nat).
      rewrite drop_alter'. erewrite count_matching_alter.
      2: by rewrite lookup_drop.
      simpl.
      rewrite Nat.add_0_r Nat.sub_0_r. lia.
    }
    rewrite alter_length drop_alter'.
    rewrite take_alter; last by lia.
    iFrame "HRs".
    iAssert (rendezvous_cancelled γtq (deqFront + z)) as "#$".
    {
      iExists γt, th. iApply (own_mono with "HFrag").
      apply auth_included; split; first done.
      apply prod_included'; split; first by apply ucmra_unit_least.
      rewrite list_op_singletonM. apply list_singletonM_included.
      rewrite list_lookup_singletonM.
      eexists. split; first done.
      apply prod_included'; split; simpl; last done.
      apply prod_included'; split; simpl; last done.
      apply ucmra_unit_least.
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
    repeat rewrite count_matching_app.
    repeat rewrite replicate_plus.
    repeat rewrite big_sepL_app.
    iDestruct "HEs" as "($ & HE & $)".
    iDestruct "HRRs" as "($ & HRR & $)".
    assert (deqFront + z < length l)%nat.
    by apply lookup_lt_is_Some; eauto.
    rewrite Nat.add_0_r take_length_le; last lia.
    simpl.

    iDestruct "HRR" as (ℓ) "HRR". iExists ℓ.
    iDestruct "HRR" as "($ & (Hℓ & HNoPerms & $) & $ & HCancHandle)".
    iFrame "HInhToken".
    iLeft.
    iFrame.
    rewrite -own_op.
    iApply (own_mono with "HFrag").
    apply auth_included; split; first done.
    apply prod_included'; split; simpl; first done.
    rewrite list_op_singletonM. rewrite ucmra_unit_right_id.
    apply list_singletonM_included.
    rewrite list_lookup_singletonM.
    eexists. split; first done.
    apply prod_included'; split; simpl; last by apply ucmra_unit_least.
    apply prod_included'; split; simpl. done.
    apply ucmra_unit_least.
  }
Qed.

Lemma rendezvous_done_from_auth γtq i γt th d l deqFront:
  l !! i = Some (Some d) ->
  (d = cellFilled ∨ ∃ v, d = cellInhabited γt th (Some v)) ->
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
  destruct d; first done. destruct Hd as [|[? Hd]]; simplify_eq.
  apply prod_included; simpl; split; last done.
  apply prod_included'; simpl; split; last done.
  apply ucmra_unit_least.
Qed.

Lemma do_cancel_rendezvous_spec E R γa γtq γe γd eℓ epℓ dℓ dpℓ l deqFront i j:
  find_index still_present (drop deqFront l) = Some j ->
  inhabitant_token γtq i -∗
  ▷ is_thread_queue E R γa γtq γe γd eℓ epℓ dℓ dpℓ l deqFront ==∗ ▷ (
  (∃ γt th, ⌜l !! i = Some (Some (cellInhabited γt th None))⌝ ∧
    is_thread_queue E R γa γtq γe γd eℓ epℓ dℓ dpℓ
      (alter (fun _ => Some (cellInhabited γt th (Some cellCancelled))) i l)
      (if (decide (i < deqFront)%nat) then (deqFront + S j)%nat else deqFront) ∗
    canceller_token γtq i ∗
    rendezvous_cancelled γtq i ∨

    ⌜l !! i = Some (Some (cellInhabited γt th (Some cellResumed)))⌝ ∧
    is_thread_queue E R γa γtq γe γd eℓ epℓ dℓ dpℓ l (deqFront + S j)%nat ∗
    (∃ (ℓ: loc), array_mapsto segment_size γa i ℓ ∗ ▷ ℓ ↦ RESUMEDV) ∗
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
        intros [_ (γt' & th' & HEl')].
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
    iDestruct "HRest" as (enqIdx deqIdx) "(HIt1 & HIt2 & HPerm & HPerm' & >%)".
    iExists enqIdx, deqIdx. iFrame.
    iPureIntro.
    rewrite alter_length.
    destruct (decide (i < deqFront)%nat).
    2: done.
    repeat split; try lia.
    assert (deqFront + j < length l)%nat; last lia.
    apply lookup_lt_is_Some.
    apply find_index_Some in HFindIndex.
    destruct HFindIndex as [(v & HEl'' & HPres) _].
    rewrite lookup_drop in HEl''. eauto.
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
      intros [_ (γt' & th' & HEl')].
      apply find_index_Some in HFindIndex.
      destruct HFindIndex as [(v & HEl'' & HPres) _].
      rewrite lookup_drop in HEl''.
      replace (deqFront + S j - 1)%nat with (deqFront + j)%nat in HEl' by lia.
      simplify_eq.
      contradiction.
    }
    iDestruct "HRest" as (enqIdx deqIdx) "(HIt1 & HIt2 & HPerm & HPerm' & >%)".
    iExists enqIdx, deqIdx. iFrame.
    iPureIntro.
    repeat split; try lia.
    assert (deqFront + j < length l)%nat; last lia.
    apply lookup_lt_is_Some.
    apply find_index_Some in HFindIndex.
    destruct HFindIndex as [(v & HEl'' & HPres) _].
    rewrite lookup_drop in HEl''. eauto.
  }
Qed.

Lemma fmap_is_map {A B} (f: A -> B) (l: list A): f <$> l = map f l.
Proof. auto. Qed.

Theorem resume_rendezvous_spec E R γa γtq γe γd i ℓ:
  inv N (cell_invariant γtq γa i ℓ) -∗
  deq_front_at_least γtq (S i) -∗
  array_mapsto segment_size γa i ℓ -∗
  iterator_issued γd i -∗
  let ap := tq_ap γtq γe in
  <<< ∀ l deqFront, ▷ cell_list_contents E R γa γtq γe γd l deqFront >>>
    getAndSet #ℓ RESUMEDV @ ⊤ ∖ ↑N
  <<< ∃ v, ⌜l !! i = Some None⌝ ∧ ⌜v = NONEV⌝ ∧
             rendezvous_filled γtq i ∗
           ▷ E ∗
           ▷ cell_list_contents E R γa γtq γe γd
             (alter (fun _ => Some cellFilled) i l) deqFront ∨

           (∃ γt th, ⌜l !! i = Some (Some (cellInhabited γt th None))⌝ ∧
           ⌜v = InjLV #th⌝ ∧
           rendezvous_resumed γtq i ∗
           ▷ E ∗
           ▷ cell_list_contents E R γa γtq γe γd
           (alter (fun _ => Some (cellInhabited γt th (Some cellResumed))) i l) deqFront ∗
           resumer_token γtq i ∨

           ⌜l !! i = Some (Some (cellInhabited γt th (Some cellCancelled)))⌝ ∧
           (⌜v = CANCELLEDV⌝ ∧
            awakening_permit γtq ∨
           ⌜v = InjLV #th⌝ ∧
           rendezvous_cancelled γtq i ∗
           ▷ rendezvous_thread_handle γtq γt th i ∗
           thread_doesnt_have_permits γt ∗
           ▷ E ∗ ▷ resumer_token γtq i) ∗
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

  awp_apply getAndSet_spec.
  iInv N as "HInv".
  iApply (aacc_aupd_commit with "AU"); first done.
  iIntros (l deqFront) "(>% & #HNotDone & >HAuth & HEs & HRs & HCellResources)".
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
    iDestruct "HInv" as "[[>HCancHandle >Hℓ]|>#HCellInit]".
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
      - simpl. rewrite Some_included_total.
        intros HH.
        apply prod_included in HH; simpl in HH.
        destruct HH as [HH _].
        apply prod_included in HH; simpl in HH.
        destruct HH as [_ HH].
        apply mnat_included in HH.
        lia.
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

    remember (alter (fun _ => Some cellFilled) i l) as l'.

    iMod (own_update _ _ (● cell_list_contents_auth_ra l' deqFront ⋅
                            (◯ (ε, {[i := (ε, cellDoneO, Some (to_agree cellFilled))]}) ⋅
                             ◯ (ε, {[i := (ε, cellDoneO, ε)]}))
                         )
            with "HAuth") as "[HAuth [HFrag1 HFrag2]]".
    {
      rewrite -auth_frag_op -pair_op list_op_singletonM ucmra_unit_left_id.
      rewrite -pair_op ucmra_unit_right_id -core_id_dup.
      apply auth_update_alloc. unfold cell_list_contents_auth_ra.
      replace (length l') with (length l).
      2: by subst; rewrite alter_length.
      apply prod_local_update'; simpl.
      apply prod_local_update_2.
      { subst. rewrite drop_alter //. lia. }
      repeat rewrite -fmap_is_map.
      subst.
      rewrite (list_alter_fmap
                  _ _ (fun _ => cell_state_to_RA (Some cellFilled))).
      2: by rewrite /= List.Forall_forall. simpl.
      apply list_lookup_local_update. intros i'.
      rewrite /ε /list_unit lookup_nil.
      destruct (nat_eq_dec i i').
      {
        subst. rewrite list_lookup_alter. repeat rewrite map_lookup.
        rewrite list_lookup_singletonM.
        rewrite HIsSome. simpl.
        apply option_local_update'.
        apply prod_local_update; simpl.
        2: by apply alloc_option_local_update.
        apply prod_local_update_2.
        apply mnat_local_update. lia.
      }
      rewrite list_lookup_alter_ne; try done.
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
      apply prod_included'; simpl. split; first done.
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
    replace (alter (fun _ => Some cellFilled) i l)
            with (alter (fun _ => Some cellFilled) (length (take i l) + O)%nat l).
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
    iDestruct (big_sepL_lookup_alter_abort
                 i O (fun _ => Some (cellInhabited γt th (Some cellResumed)))
                 with "[HCellResources]")
      as "[HR HCellRRsRestore]"; simpl; try done.
    simpl.
    iDestruct "HR" as (ℓ') "(>HArrMapsto' & HThread & HIsSus & HCancHandle)".
    iDestruct (array_mapsto_agree with "HArrMapsto' HArrMapsto") as %->.
    iDestruct "HThread" as "(Hℓ & >HNotPerms & #HRend)".
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
    iRight.
    iExists γt, th. iLeft.

    iSplitR; first done. iSplitR; first done.
    rewrite /cell_list_contents alter_length.
    iAssert (⌜deqFront <= length l⌝)%I as "$". done.
    replace (alter (fun _ => Some (cellInhabited γt th (Some cellResumed))) i l) with
        (alter (fun _ => Some (cellInhabited γt th (Some cellResumed)))
               (length (take i l) + O)%nat l).
    2: rewrite -plus_n_O take_length_le; first done.
    2: lia.
    remember (_ + _)%nat as K.
    replace l with (take i l ++ Some (cellInhabited γt th None) :: drop (S i) l).
    2: by rewrite take_drop_middle. subst.
    rewrite alter_app_r.
    repeat rewrite take_app_ge.
    all: rewrite take_length_le; try lia.
    destruct (deqFront - i)%nat eqn:Z. lia.
    repeat rewrite count_matching_app. repeat rewrite replicate_plus.
    repeat rewrite big_sepL_app. simpl.
    iDestruct "HEs" as "(HEsH & $ & HEsT)".
    iDestruct "HRs" as "(HRsH & HR & HRsT)".
    iDestruct ("HCellRRsRestore" with "[HIsRes HArrMapsto' HIsSus HCancHandle Hℓ HR HNotPerms]")
      as "(HCellRRsH & HCellR & HCellRRsT)".
    { iExists _. iFrame "HArrMapsto' HIsRes HCancHandle HIsSus HRend". iRight. iFrame. }
    repeat rewrite -big_sepL_later.
    iFrame.
    unfold cell_list_contents_auth_ra.
    rewrite /rendezvous_resumed /rendezvous_done /rendezvous_state.
    iMod (own_update with "HAuth") as "[HAuth [HFrag HRes]]".
    2: {
      iSplitL "HFrag".
      by iExists γt, th; iFrame.
      iFrame "HAuth HRes".
      repeat rewrite drop_app_ge take_length_le; try lia.
      rewrite Z. simpl. done.
    }
    rewrite -auth_frag_op -pair_op ucmra_unit_right_id list_op_singletonM.

    apply auth_update_alloc, prod_local_update'; simpl.
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
      apply prod_local_update, mnat_local_update; simpl.
      apply prod_local_update_2. simpl.
      by apply alloc_option_local_update.
      by rewrite ucmra_unit_right_id; lia.
  }

  iDestruct (big_sepL_lookup_acc with "[HCellResources]")
    as "[HR HCellRRsRestore]"; simpl; try done.
  simpl.

  repeat rewrite -big_sepL_later.
  destruct d; simpl.
  2: { (* Resumed? Impossible. *)
    iDestruct "HR" as (?) "(_ & _ & _ & >HIsRes' & _)".
    iDestruct (iterator_issued_exclusive with "HIsRes HIsRes'") as %[].
  }

  { (* Cancelled. *)
    iDestruct "HR" as (ℓ') "(>HArrMapsto' & #HRend & HIsSus & HInhToken' & HH)".
    iDestruct (array_mapsto_agree with "HArrMapsto' HArrMapsto") as %->.

    iMod (rendezvous_done_from_auth with "HAuth") as "[HAuth HCanc]"; first done.
    by right; eauto.

    iDestruct "HH" as "[[Hℓ (HResTok & HE & HCancHandle & >HNoPerms & HAwak)]|
      [(_ & >HIsRes' & _)|(Hℓ & HCancTok &
      [(>HIsRes' & _)|(HResTok & >HAwak)])]]".
    3: by iDestruct (iterator_issued_exclusive with "HIsRes HIsRes'") as %[].
    2: by iDestruct (iterator_issued_exclusive with "HIsRes HIsRes'") as %[].
    1: remember (InjLV #th) as v.
    2: remember CANCELLEDV as v.
    all: iAssert (▷ ℓ ↦ v ∧ ⌜val_is_unboxed v⌝)%I with "[Hℓ]" as "HAacc";
      first by (iFrame; iPureIntro; subst; done).
    iAaccIntro with "HAacc"; iFrame "HNotDone".
    {
      iIntros "[Hℓ _]". iSplitR "HInv HIsRes"; last by iIntros "!> $ !>"; iFrame.
      iFrame "HEs HRs HAuth". iSplitR; first done. iApply "HCellRRsRestore".
      iExists _. iFrame "HArrMapsto' HIsSus HInhToken' HRend".
      iLeft; by iFrame.
    }
    {
      iIntros "Hℓ !>". iExists v. iSplitR "HInv".
      2: by iIntros "$ !>".
      iRight. iExists γt, th. iRight. iLeft.

      iSplitR; first done.
      iSplitL "HCanc HResTok HE HNoPerms"; first iRight.
      { iFrame "HRend"; iFrame. iSplitR; first done. by iExists _, _. }
      iSplitR; first done. iFrame "HEs HRs HAuth".
      iApply "HCellRRsRestore". iExists _.
      iFrame "HArrMapsto HRend HIsSus HInhToken'".
      iRight. iLeft.
      iFrame. iRight. iFrame.
    }

    iAaccIntro with "HAacc"; iFrame "HNotDone".
    {
      iIntros "[Hℓ _]". iSplitR "HInv HIsRes"; last by iIntros "!> $ !>"; iFrame.
      iFrame "HEs HRs HAuth". iSplitR; first done. iApply "HCellRRsRestore".
      iExists _. iFrame "HArrMapsto' HIsSus HInhToken' HRend".
      iRight; iRight; iFrame. iRight. by iFrame.
    }
    {
      iIntros "Hℓ !>". iExists v. iSplitR "HInv".
      2: by iIntros "$ !>".
      iRight. iExists γt, th. iRight. iLeft.

      iSplitR; first done.
      iDestruct "HAwak" as "[HAwak|[HIsRes' _]]".
      2: by iDestruct (iterator_issued_exclusive with "HIsRes HIsRes'") as %[].
      iSplitL "HAwak"; first by iLeft; iFrame; iPureIntro; auto.
      iSplitR; first done. iFrame "HEs HRs HAuth".
      iApply "HCellRRsRestore". iExists _.
      iFrame "HArrMapsto HRend HIsSus HInhToken'".
      iRight. iLeft.
      iFrame. iLeft. iFrame.
    }
  }
  (* Abandoned *)

  iMod (rendezvous_done_from_auth with "HAuth") as "[HAuth HIsAbandoned]"; first done.
  right; eauto.
  iAssert (rendezvous_done γtq i (cellInhabited γt th (Some cellAbandoned)))
             with "HIsAbandoned" as "HIsAbandoned".

  iDestruct "HR" as (?) "(>HArrMapsto' & #HRend & HCancHandle & HIsSus & HInh & HDeqFront & HH)".
  iDestruct "HH" as "[>HIsRes'|(HE & Hℓ & >HNoPerms)]".
  by iDestruct (iterator_issued_exclusive with "HIsRes HIsRes'") as %[].
  iDestruct (array_mapsto_agree with "HArrMapsto' HArrMapsto") as %->.

  iAssert (▷ ℓ ↦ InjLV #th ∧ ⌜val_is_unboxed (InjLV #th)⌝)%I
    with "[Hℓ]" as "HAacc".
  by iFrame.

  iAaccIntro with "HAacc"; iFrame "HNotDone".
  {
    iIntros "[Hℓ _] !>".
    iSplitR "HInv HIsRes".
    {
      iFrame. iSplitR; first done. iApply "HCellRRsRestore".
      iExists _; iFrame "HArrMapsto'"; iFrame.
      iFrame "HRend".
      iRight. iFrame.
    }
    iIntros "$ !>". iFrame.
  }

  iIntros "Hℓ !>". iExists _.
  iSplitR "HInv".
  2: by iIntros "$ !>".
  iRight. iExists γt, th.
  repeat iRight.

  iSplitR; first done.
  iSplitR; first by eauto.
  iFrame.
  iSplitL "HIsAbandoned".
  by iExists _, _.
  iSplitR; first done.
  iApply "HCellRRsRestore".
  iExists _; iFrame "HArrMapsto'". by iFrame.
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
  iFrame "HDeqFront".

  iMod (own_update with "HAuth") as "[$ HFrag]".
  2: {
    iSplitR "HFrag".
    2: by iExists _, _; iFrame.
    iSplitR; first done.
    iSplitR.
    2: by iExists ℓ; iFrame "HArrMapsto"; iRight; iFrame.
    rewrite drop_app_ge take_length_le; try lia.
    rewrite Z. simpl.
    rewrite drop_drop /= plus_n_Sm -Z.
    by replace (i + (deqFront - i))%nat with deqFront by lia.
  }

  apply auth_update_alloc, prod_local_update; simpl.
  {
    apply prod_local_update; simpl.
    {
      simpl.
      rewrite app_length /= drop_length take_length_le /=.
      replace (i + S (length l - S i))%nat with (length l).
      done.
      all: lia.
    }
    rewrite drop_app_ge take_length_le.
    rewrite Z /= drop_drop /= plus_n_Sm -Z.
    by replace (i + (deqFront - i))%nat with deqFront by lia.
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
  apply mnat_local_update.
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
  ∃ γt th, ⌜l !! i = Some (Some (cellInhabited γt th (Some cellCancelled)))⌝.
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
    rewrite mnat_included. lia.
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
  all: by iDestruct (cell_cancellation_handle'_not_cancelled with "HCancHandle HCanc")
      as %[].
Qed.

Lemma cancelled_cell_is_cancelled_rendezvous S R γa γtq γe γd ℓ i l deqFront:
  cell_is_cancelled segment_size γa i -∗
  cell_invariant γtq γa i ℓ -∗ cell_list_contents S R γa γtq γe γd l deqFront -∗
  ∃ γt th, ⌜l !! i = Some (Some (cellInhabited γt th (Some cellCancelled)))⌝.
Proof.
  iIntros "HCanc HCellInv HListContents".
  iDestruct "HCellInv" as "[[HCancHandle _]|HInit]".
  by iDestruct (cell_cancellation_handle'_not_cancelled with "HCancHandle HCanc")
    as %[].
  by iApply (cancelled_cell_is_cancelled_rendezvous' with "HCanc HInit").
Qed.

Lemma awakening_permit_from_cancelled_cell' E R γa γtq γe γd i γt th:
  cell_is_cancelled segment_size γa i -∗
  iterator_issued γd i -∗
  cell_resources E R γtq γa γe γd i (Some (cellInhabited γt th (Some cellCancelled))) -∗
  cell_resources E R γtq γa γe γd i (Some (cellInhabited γt th (Some cellCancelled))) ∗
  awakening_permit γtq.
Proof.
  simpl. iIntros "HCellCanc HIsRes HR".
  iDestruct "HR" as (?) "(HArrMapsto & $ & $ & $ & HH)".
  iDestruct "HH" as "[(_ & _ & _ & HCancHandle & _)|[(_ & HIsRes' & _)|
    (Hℓ & HCancTok & [[HIsRes' _]|[HResTok [HAwak|[HIsRes' _]]]])]]".
  by iDestruct (cell_cancellation_handle'_not_cancelled with "HCancHandle HCellCanc") as %[].
  all: try by iDestruct (iterator_issued_exclusive with "HIsRes HIsRes'") as %[].
  iFrame "HAwak".
  iExists _. iFrame "HArrMapsto". iRight. iRight. iFrame "Hℓ HCancTok".
  iRight. iFrame "HResTok". iRight. iFrame.
Qed.

Lemma awakening_permit_from_cancelled_cell E R γa γtq γe γd deqFront l γt th i:
  l !! i = Some (Some (cellInhabited γt th (Some cellCancelled))) ->
  cell_is_cancelled segment_size γa i -∗
  iterator_issued γd i -∗
  cell_list_contents E R γa γtq γe γd l deqFront -∗
  awakening_permit γtq ∗ cell_list_contents E R γa γtq γe γd l deqFront.
Proof.
  iIntros (HEl) "HCanc HIsRes HListContents".
  iDestruct (cell_list_contents_lookup_acc with "HListContents")
    as "[HR HListContents]"; first done.
  iDestruct (awakening_permit_from_cancelled_cell' with "HCanc HIsRes HR")
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
    (* deqIdx' <= the head id * segment_size *)
    assert (hId = deqIdx' `div` Pos.to_nat segment_size)%nat as ->.
    { eapply find_segment_id_bound; try lia. done. }
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

  iAssert (□ [∗ list] k ∈ seq deqIdx' (tId * Pos.to_nat segment_size - deqIdx')%nat,
           |={⊤}=> cell_is_cancelled segment_size γa k ∗ rendezvous_initialized γtq k)%I
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
                   "HCanc HInit HListContents") as (? ?) "#>%".
    iDestruct "HRest" as "(HAwak & HSusp & >[[% %] %])".
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
    rewrite big_sepL_sep.
    iSplitL.
    2: {
      repeat rewrite big_sepL_forall.
      iIntros (? x HEl).
      iSpecialize ("HEv'" $! _ x).
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

  (* *)

  iAssert ([∗ list] k ∈ seq deqIdx' (tId * Pos.to_nat segment_size - deqIdx'),
           ▷ ∃ γt th, ⌜l !! k = Some (Some (cellInhabited γt th (Some cellCancelled)))⌝)%I
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

  iDestruct (big_sepL_lookup _ _ O with "HEv''") as %(? & ? & HEl).
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
      iDestruct "HH" as %HH.
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

    iAssert (∀ i, ⌜(i < len)%nat⌝ -∗ ⌜∃ γt th, drop start l !! i =
            Some (Some (cellInhabited γt th (Some cellCancelled)))⌝)%I as "#HEv'''".
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
      destruct HH as (γt & th & HH).
      exists γt, th.
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
    iDestruct ("HEv'''" $! O with "[]") as %(? & ? & HIsCanc).
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
                 ∃ γt th, l !! k = Some (Some (cellInhabited γt th (Some cellCancelled)))⌝)%I as %HCanc.
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
    assert (newDeqFront > 0 ∧ (exists γt th, l !! (newDeqFront - 1)%nat = Some (Some (cellInhabited γt th (Some cellCancelled)))) -> False) as HH by assumption.
    apply HH. split; first by lia.
    apply HCanc.
    lia.
  }
  iSplitR; first done.
  iExists _, _. iFrame "HEnqIt HDeqCounter".
  iSplitL "HDeqLoc".
  {
    iDestruct "HDeqLoc" as (? ? ?) "[H1 H2]".
    iExists _; iSplitR; first by iPureIntro; lia.
    iExists _; by iFrame.
  }
  iFrame.
  iSplitL.
  2: by iPureIntro; lia.

  iDestruct "HRest'" as ">HRest'".
  iCombine "HRest' HAwaks" as "HAwaks".
  rewrite -big_sepL_app seq_app.
  2: lia.
  done.

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
  by apply mnat_included.
Qed.

Theorem iterator_move_ptr_forward_spec ap γa γ cℓ (ℓ: loc) (pℓ: loc) i id:
  ⌜(id * Pos.to_nat segment_size <= i)%nat⌝ -∗
  iterator_counter_at_least γ i -∗
  segment_location γa id ℓ -∗
  <<< ∀ (i': nat), ▷ is_infinite_array segment_size ap γa ∗
                   iterator_points_to segment_size γa γ cℓ pℓ i' >>>
    move_ptr_forward #pℓ #ℓ @ ⊤
    <<< ▷ is_infinite_array segment_size ap γa ∗
        iterator_points_to segment_size γa γ cℓ pℓ i', RET #() >>>.
Proof.
  iIntros (HLt) "#HCtrAtLeast #HSegLoc". iIntros (Φ) "AU". iLöb as "IH".
  wp_lam. wp_pures.

  wp_bind (!_)%E.
  iMod "AU" as (?) "[[HIsInf [HCtr HPtr]] [HClose _]]".
  iDestruct "HPtr" as (id' ? ℓ') "[#HSegLoc' Hℓ']".
  wp_load.
  iMod ("HClose" with "[-]") as "AU".
  { iFrame. iExists _. iSplitR. 2: iExists _; iFrame. done. done. }

  iIntros "!>".
  wp_pures.

  awp_apply segment_id_spec. iApply (aacc_aupd_abort with "AU"); first done.
  iIntros (?) "[HIsInf HIt]".
  iDestruct (is_segment_by_location with "HSegLoc' HIsInf")
    as (? ?) "[HIsSeg HArrRestore]".
  iAaccIntro with "HIsSeg".
  { iIntros "HIsSeg". iDestruct ("HArrRestore" with "HIsSeg") as "$".
    iFrame "HIt". by iIntros "!> $ !>". }
  iIntros "HIsSeg".
  iDestruct ("HArrRestore" with "[HIsSeg]") as "$"; first by iFrame.
  iFrame "HIt".
  iIntros "!> AU !>".

  awp_apply segment_id_spec. iApply (aacc_aupd with "AU"); first done.
  iIntros (?) "[HIsInf HIt]".
  iDestruct (is_segment_by_location with "HSegLoc HIsInf")
    as (? ?) "[HIsSeg HArrRestore]".
  iAaccIntro with "HIsSeg".
  { iIntros "HIsSeg". iDestruct ("HArrRestore" with "HIsSeg") as "$".
    iFrame "HIt". by iIntros "!> $ !>". }
  iIntros "HIsSeg".
  iDestruct ("HArrRestore" with "[HIsSeg]") as "$"; first by iFrame.
  iFrame "HIt".
  iIntros "!>".

  destruct (bool_decide (id <= id')) eqn:Z.
  {
    iRight. iIntros "HΦ !>". wp_pures. rewrite Z.
    by wp_pures.
  }

  iLeft.
  iIntros "AU !>". wp_pures. rewrite Z. wp_pures.

  wp_bind (CmpXchg _ _ _).
  iMod "AU" as (?) "[[HIsInf [HCtr HPtr]] HClose]".
  iDestruct "HPtr" as (id'' ? ℓ'') "[#HSegLoc'' Hℓ'']".

  destruct (decide (ℓ'' = ℓ')); subst.
  {
    wp_cmpxchg_suc.
    iDestruct (iterator_points_to_at_least with "HCtrAtLeast HCtr") as %HCtr.
    iMod ("HClose" with "[-]") as "HΦ".
    { iFrame. iExists _; iSplitR. 2: iExists _; by iFrame. iPureIntro. lia. }
    iModIntro. by wp_pures.
  }
  {
    wp_cmpxchg_fail.
    iDestruct "HClose" as "[HClose _]".
    iMod ("HClose" with "[-]") as "AU".
    { iFrame. iExists _; iSplitR. 2: iExists _; by iFrame. iPureIntro. lia. }
    iModIntro. wp_pures. iApply ("IH" with "AU").
  }
Qed.

Theorem try_deque_thread_spec E R γa γtq γe γd (eℓ epℓ dℓ dpℓ: loc):
  ▷ awakening_permit γtq -∗
  <<< ∀ l deqFront, ▷ is_thread_queue E R γa γtq γe γd eℓ epℓ dℓ dpℓ l deqFront >>>
  ((try_deque_thread segment_size) #dpℓ) #dℓ @ ⊤ ∖ ↑N
  <<< ∃ (v: val), ▷ E ∗ (∃ i,
     (⌜l !! i = Some None⌝ ∧ ⌜v = #()⌝ ∧
                     ▷ is_thread_queue E R γa γtq γe γd eℓ epℓ dℓ dpℓ
                            (alter (fun _ => Some cellFilled) i l) deqFront) ∗
                            rendezvous_filled γtq i ∨
   ∃ γt (th: loc),
       ▷ rendezvous_thread_handle γtq γt th i ∗ (
      ⌜l !! i = Some (Some (cellInhabited γt th None))⌝ ∧ ⌜v = #th⌝ ∧
      ▷ is_thread_queue E R γa γtq γe γd eℓ epℓ dℓ dpℓ
        (alter (fun _ => Some (cellInhabited γt th (Some cellResumed))) i l)
        deqFront ∗ rendezvous_resumed γtq i ∗ resumer_token γtq i ∨

      (⌜l !! i = Some (Some (cellInhabited γt th (Some cellCancelled)))⌝ ∗
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
    iApply big_sepL_forall. iIntros (k d' HEl).
    iRight. simpl.
    iApply (iterator_counter_at_least_mono with "HDAtLeast").
    apply seq_lookup' in HEl.
    simpl in *. destruct HEl as [<- HEl].
    assert (forall a x, (a > 0)%nat -> (x `div` a * a <= x)%nat) as HOk.
    {
      clear. intros ? ? H.
      rewrite Nat.mul_comm.
      apply Nat.mul_div_le.
      lia.
    }
    specialize (HOk (Pos.to_nat segment_size) d).
    lia.
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

  replace (d `rem` Pos.to_nat segment_size) with
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
    by apply mnat_included.
  }
  simpl.
  iAssert (▷ deq_front_at_least γtq (S d))%I as "#HDeqFront".
  {
    iDestruct "HRest" as "(_ & HH)".
    iDestruct "HH" as (? deqIdx) "(_ & [>HDeqCtr _] & _ & _ & >%)".
    iDestruct (iterator_points_to_at_least with "HDAtLeast HDeqCtr") as "%".
    iApply (own_mono with "HFrag").

    apply auth_included. simpl. split; first done.
    repeat (apply prod_included'; simpl; split; try done).
    apply mnat_included. lia.
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
      intros (HDeqFront & γt & th & HEl).
      destruct (decide (d = (deqFront' - 1)%nat)).
      {
        subst.
        rewrite list_lookup_alter in HEl.
        destruct (_ !! (deqFront' - 1)%nat); simplify_eq.
      }
      rewrite list_lookup_alter_ne in HEl; try done.
      by eauto.
    }
    iDestruct "HRest" as (enqIdx deqIdx) "HH".
    iExists enqIdx, deqIdx.
    by rewrite alter_length.
  }

  iDestruct "HH" as (γt th)
    "[(HEl & -> & #HRendRes & HE & HListContents & HResumerToken)|
    [(% & HH & HIsRes & HListContents)|
    (% & -> & HRendAbandoned & HE & HNoPerms & HListContents)]]".
  3: { (* Abandoned *)
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
    iRight.
    repeat (iSplitR; first by iPureIntro).
    iSplitL "HRendAbandoned". by eauto with iFrame.
    by iFrame.
  }
  2: { (* Cancelled *)
    iDestruct "HH" as "[[HH HAwak]|(-> & HCanc & #HRend & HNoPerms & HE & HResTok)]".
    {
      iLeft. iFrame.
      iIntros "!> AU !>". wp_pures.
      iDestruct "HH" as "->"; wp_pures. iApply ("IH" with "HAwak AU").
    }
    iRight. iExists _. iFrame "HE". iSplitL.
    2: by iIntros "!> HΦ !>"; wp_pures.
    iExists _. iRight. iExists _, _. iFrame "HRend".
    iRight. iSplitL "HCanc".
    { iLeft. iFrame. done. }
    by iFrame.
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
      erewrite list_lookup_alter.
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
  rewrite alter_length.
  iFrame "HRendRes".
  iFrame.
  iPureIntro.
  intros (HLt & γt' & th' & HEl'').
  destruct (decide (d = (deqFront' - 1)%nat)).
  {
    subst. rewrite list_lookup_alter in HEl''.
    destruct (_ !! (deqFront' - 1)%nat); simplify_eq.
  }
  rewrite list_lookup_alter_ne in HEl''; try done.
  by eauto.
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
  iDestruct "HRest" as (enqIdx ?) "(>HEnqIt & >HDeqIt & HAwaks & >HSusps & >%)".
  iDestruct "HListContents" as "(HLC1 & HLC2 & >HAuth & HLC3)".
  iAssert (⌜(enqIdx < length cells)%nat⌝)%I as %HEnqLtLen.
  {
    rewrite /suspension_permit.
    iAssert (own γtq (◯ (S enqIdx,ε, ε))) with "[HSusp HSusps]" as "HSusp".
    {
      clear.
      iInduction enqIdx as [|enqIdx'] "IH"; first done. simpl.
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
  2: iAssert (exists_list_element γtq enqIdx) with "HFrag" as "#HElExists".
  {
    apply auth_update_core_id; first by apply _.
    apply prod_included; simpl; split.
    by apply ucmra_unit_least.
    apply list_lookup_included.
    revert HEnqLtLen.
    clear.
    intros ? i.
    rewrite -fmap_is_map list_lookup_fmap.
    destruct (decide (i >= S enqIdx)).
    {
      remember (cells !! i) as K. clear HeqK.
      rewrite lookup_ge_None_2.
      2: rewrite list_singletonM_length; lia.
      by apply option_included; left.
    }
    assert (i < length cells)%nat as HEl by lia.
    apply lookup_lt_is_Some in HEl.
    destruct HEl as [? ->]. simpl.
    destruct (decide (i = enqIdx)).
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
  change (own _ (◯ _)) with (iterator_issued γe enqIdx).
  iFrame.
  iSplitR "HIsSus HNoPerms".
  {
    iSplitR; first done.
    iExists _, _. simpl.
    iAssert ([∗ list] _ ∈ seq O (S enqIdx), suspension_permit γtq)%I
            with "[HSusps HSusp]" as "$".
    {
      simpl. iFrame.
      iApply (big_sepL_forall' with "HSusps").
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
  iAssert (⌜(enqIdx `div` Pos.to_nat segment_size <= segId)%nat⌝)%I as "%".
  by iDestruct "HRest'" as "[(% & <-)|(% & % & _)]"; iPureIntro; lia.
  iDestruct (big_sepL_lookup _ _ (enqIdx `div` Pos.to_nat segment_size)%nat with "HInvs") as "HInv".
  by apply seq_lookup; lia.
  iDestruct (cell_invariant_by_segment_invariant
               _ _ _ _ (enqIdx `mod` Pos.to_nat segment_size)%nat with "HInv") as "HInv'".
  by apply Nat.mod_upper_bound; lia.
  simpl.
  rewrite Nat.mul_comm -Nat.div_mod; try lia.
  iDestruct "HInv'" as (ℓ) "(HCellInv & >HMapsTo)".
  iFrame.
  iIntros "!> AU !>".

  wp_pures.

  destruct (decide (enqIdx `div` Pos.to_nat segment_size = segId)%nat).
  2: {
    iDestruct "HRest'" as "[[% ->]|HC]".
    {
      exfalso.
      assert (enqIdx `div` Pos.to_nat segment_size < segId)%nat by lia.
      assert ((segId * Pos.to_nat segment_size) `div` Pos.to_nat segment_size <=
              enqIdx `div` Pos.to_nat segment_size)%nat as HContra.
      by apply Nat.div_le_mono; lia.
      rewrite Nat.div_mul in HContra; lia.
    }
    iDestruct "HC" as "(% & % & HCanc)".
    rewrite segments_cancelled__cells_cancelled.
    remember (Pos.to_nat segment_size) as P.
    iAssert (cell_is_cancelled segment_size γa
              (P * enqIdx `div` P + enqIdx `mod` P)%nat) as "HCellCanc".
    {
      rewrite Nat.mul_comm.
      iApply (big_sepL_lookup with "HCanc").
      apply seq_lookup.
      assert (enqIdx `mod` P < P)%nat by (apply Nat.mod_upper_bound; lia).
      destruct (segId - enqIdx `div` P)%nat eqn:Z; try lia.
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
      specialize (HValid enqIdx). move: HValid.
      rewrite list_lookup_singletonM map_lookup HEl /= Some_included_total.
      intros HValid.
      apply prod_included in HValid; simpl in *; destruct HValid as [HValid _].
      apply prod_included in HValid; simpl in *; destruct HValid as [_ HValid].
      apply mnat_included in HValid. lia.
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
  by move: (Nat.mul_div_le enqIdx (Pos.to_nat segment_size)); lia.
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
  replace (enqIdx `rem` _) with (Z.of_nat (enqIdx `mod` Pos.to_nat segment_size)%nat).
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
  intros (HLt & γt' & th' & HEl).
  destruct (decide (enqIdx = (deqFront - 1)%nat)).
  {
    subst. rewrite list_lookup_alter in HEl.
    destruct (_ !! (deqFront - 1)%nat); simpl in *; discriminate.
  }
  rewrite list_lookup_alter_ne in HEl; eauto.
Qed.

Theorem new_thread_queue_spec S R:
  {{{ True }}}
    new_thread_queue segment_size #()
  {{{ γa γtq γe γd eℓ epℓ dℓ dpℓ, RET ((#epℓ, #eℓ), (#dpℓ, #dℓ));
      is_thread_queue S R γa γtq γe γd eℓ epℓ dℓ dpℓ [] 0 }}}.
Proof.
  iIntros (Φ) "_ HPost".
  wp_lam.
  iMod (own_alloc (● (GSet (set_seq 0 0), 0%nat: mnatUR))) as (γd) "HAuthD".
  { simpl. apply auth_auth_valid, pair_valid; split; done. }
  iMod (own_alloc (● (GSet (set_seq 0 0), 0%nat: mnatUR))) as (γe) "HAuthE".
  { simpl. apply auth_auth_valid, pair_valid; split; done. }
  iMod (own_alloc (● (0%nat, (0%nat, 0%nat: mnatUR), []))) as (γtq) "HAuth".
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
    rewrite auth_frag_valid pair_valid list_op_singletonM list_lookup_valid /=.
    intros [_ HValid]. specialize (HValid i). move: HValid.
    rewrite list_lookup_singletonM.
    intros HValid.
    destruct HValid as [[[_ []] _] _].
  }
  iDestruct "HRes" as (ℓ) "(HArrMapsto & HTH & HIsSus & HIsRes & HCancHandle &
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
  <<< ∃ (v: bool), ▷ is_thread_queue E R γa γtq γe γd eℓ epℓ dℓ dpℓ l deqFront ∗
    (⌜v = false⌝ ∗ ▷ awakening_permit γtq ∨ ⌜v = true⌝), RET #v >>>.
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
  iIntros (l ?) "(HInfArr & HListContents & HTail')".
  iAssert (▷ ⌜∃ γt th, l !! i = Some (Some (cellInhabited γt th
                              (Some cellCancelled)))⌝)%I
          as "#>HEl".
  {
    iDestruct "HListContents" as "(_ & _ & >HAuth & _)".
    iDestruct "HRendCanc" as (? ?) "HRendCanc".
    iDestruct (cell_list_contents_done_agree with "HAuth HRendCanc")
              as %HOk.
    simplify_eq.
    iExists _, _. done.
  }
  iDestruct "HEl" as %(γt & th & HEl).

  iDestruct (cell_list_contents_lookup_acc with "HListContents")
    as "[HRR HListContentsRestore]"; first done.
  simpl.
  iDestruct "HRR" as (ℓ') "(#>HArrMapsto' & HRendHandle & HIsSus & >HInhTok & HH)".
  iDestruct (array_mapsto'_agree with "HArrMapsto' HArrMapsto") as %->.
  assert (inhabitant_token' γtq i (1/2)%Qp -∗
          inhabitant_token' γtq i (1/2)%Qp -∗
          inhabitant_token' γtq i (1/2)%Qp -∗ False)%I as HNoTwoCanc.
  {
    iIntros "HInhTok1 HInhTok2 HInhTok3".
    iDestruct (own_valid_3 with "HInhTok1 HInhTok2 HInhTok3") as %HValid.
    iPureIntro.
    move: HValid. rewrite -auth_frag_op -pair_op.
    repeat rewrite list_op_singletonM.
    rewrite auth_frag_valid /=. rewrite pair_valid.
    rewrite list_singleton_valid. intros [_ [[[[HPairValid _] _] _] _]].
    by compute.
  }
  iDestruct "HH" as "[(Hℓ & HResTok & HE & HCancHandle & HNoPerms & HAwak)|
    [(Hℓ & HIsRes & [(>HCancTok' & _)|(HCancHandle & HAwak)])|(_ & >HCancTok' & _)]]".
  all: try iDestruct (HNoTwoCanc with "HInhTok HCancTok HCancTok'") as %[].

  2: {
    iAssert (▷ ℓ ↦ RESUMEDV ∧ ⌜val_is_unboxed RESUMEDV⌝)%I with "[$]" as "HAacc".
    iAaccIntro with "HAacc".
    {
      iIntros "[Hℓ _]". iFrame "HCancTok".
      iIntros "!>".
      iSplitL; last by iIntros "$". iFrame.
      iApply "HListContentsRestore".
      iExists _. iFrame "HArrMapsto' HRendHandle HIsSus HInhTok".
      iRight. iLeft. iFrame. iRight. iFrame.
    }

    iIntros "Hℓ !>". iRight. iExists false.
    iSplitL.
    {
      iSplitR "HAwak"; last by iLeft; iFrame.
      iFrame.
      iApply "HListContentsRestore".
      iExists _. iFrame "HArrMapsto' HRendHandle HIsSus HInhTok".
      iRight. iRight. iFrame. iLeft. iFrame.
    }
    iIntros "HΦ' !>". wp_pures.
    by iApply "HΦ'".
  }

  iAssert (▷ ℓ ↦ InjLV #th ∧ ⌜val_is_unboxed (InjLV #th)⌝)%I with "[$]" as "HAacc".

  iAaccIntro with "HAacc".
  {
    iIntros "[Hℓ _]". iFrame "HCancTok".
    iIntros "!>".
    iSplitL; last by iIntros "$ !>".
    iFrame.
    iApply "HListContentsRestore".
    iExists _. iFrame "HArrMapsto' HRendHandle HIsSus HInhTok".
    iLeft. iFrame.
  }

  iIntros "Hℓ !>".
  iLeft.
  iSplitR "HCancHandle".
  {
    iFrame.
    iApply "HListContentsRestore".
    iExists _. iFrame "HArrMapsto' HRendHandle HIsSus HInhTok".
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
