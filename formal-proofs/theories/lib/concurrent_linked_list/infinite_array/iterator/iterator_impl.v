From SegmentQueue.lib.concurrent_linked_list.infinite_array
     Require Import array_spec array_helpers.
From SegmentQueue.util Require Import big_opL everything.
From SegmentQueue.lib.util Require Import increaseValueTo.

Section impl.

Variable (array_interface: infiniteArrayInterface).

Definition iteratorStep: val :=
  λ: "iterator",
  let: "counter" := Fst "iterator" in
  let: "ptr" := Snd "iterator" in
  let: "start" := cutoffGetPointer array_interface "ptr" in
  let: "idx" := FAA "counter" #1%nat in
  ("idx", findCellAndMoveForward array_interface "ptr" "idx" "start").

Definition iteratorStepOrIncreaseCounter: val :=
  λ: "shouldAdjust" "iterator",
  let: "counter" := Fst "iterator" in
  let: "s" := iteratorStep "iterator" in
  if: cellPointerId array_interface (Snd "s") = (Fst "s") then SOME (Snd "s")
  else (if: "shouldAdjust"
        then increaseValueTo "counter" (cellPointerId array_interface (Snd "s"))
        else #()) ;; NONE.

Definition newIterator: val :=
  λ: "ptr" "n", (ref "n", "ptr").

End impl.

From iris.program_logic Require Import atomic.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Export proofmode notation lang.
From iris.algebra Require Import excl cmra auth gset numbers.

Section proof.

Context `{heapG Σ}.

Variable (array_interface: infiniteArrayInterface).
Variable (aspc: infiniteArraySpec Σ array_interface).

Notation algebra := (authR (prodUR (gset_disjUR nat)
                                   max_natUR)).

Class iteratorG Σ := IIteratorG { iterator_inG :> inG Σ algebra }.
Definition iteratorΣ : gFunctors := #[GFunctor algebra].
Instance subG_iteratorΣ : subG iteratorΣ Σ -> iteratorG Σ.
Proof. solve_inG. Qed.

Context `{iteratorG Σ}.

Notation iProp := (iProp Σ).

Variable (NArray: namespace).
Variable (N: namespace).
Context (NNonIntersecting: NArray ## N).

Definition iterator_auth_ra n :=
  (● (GSet (set_seq 0 n), MaxNat n)).

Definition iterator_counter γ cℓ (n: nat): iProp :=
  (cℓ ↦ #n ∗ own γ (iterator_auth_ra n))%I.

Definition iterator_counter_at_least γ (n: nat): iProp :=
  own γ (◯ (ε, MaxNat n)).

Global Instance iterator_counter_at_least_persistent γ n:
  Persistent (iterator_counter_at_least γ n).
Proof. apply _. Qed.

Definition iterator_contents co γa (P: iProp) γ cℓ p n: iProp :=
  (iterator_counter γ cℓ n ∗ ([∗] replicate n P) ∗
   ∃ (id: nat), (∀ id', ⌜n ≤ id' < id⌝ -∗
                        cell_is_cancelled _ _ aspc NArray γa id' ∗
                        ∃ ℓ, infinite_array_mapsto _ _ aspc NArray co γa id' ℓ) ∗
  is_infinite_array_cutoff _ _ aspc NArray γa p id)%I.

Definition is_iterator co γa P γ v: iProp :=
  ∃ (cℓ: loc) (p: val),
    ⌜v = (#cℓ, p)%V⌝ ∧
    inv N (∃ (n: nat), iterator_contents co γa P γ cℓ p n).

Global Instance is_iterator_persistent co γa P γ v:
  Persistent (is_iterator co γa P γ v).
Proof. apply _. Qed.

Definition iterator_issued γ n :=
  own γ (◯ (GSet {[ n ]}, MaxNat (S n))).

Theorem iterator_issued_timeless γ n: Timeless (iterator_issued γ n).
Proof. apply _. Qed.

Theorem iterator_issued_exclusive γ n:
  iterator_issued γ n -∗ iterator_issued γ n -∗ False.
Proof.
  iIntros "HIss HIss'".
  iDestruct (own_valid_2 with "HIss HIss'") as %HContra.
  exfalso. revert HContra. clear. rewrite -auth_frag_op -pair_op.
  case; simpl. rewrite gset_disj_valid_op. by set_solver.
Qed.

Lemma iterator_value_increase γ (n m: nat):
  own γ (iterator_auth_ra n) ==∗
  own γ (iterator_auth_ra (n + m)) ∗
  iterator_counter_at_least γ (n + m) ∗
  [∗ list] i ∈ seq n m, iterator_issued γ i.
Proof.
  iIntros "H●".
  iMod (own_update with "H●") as "[$ [$ HPermits]]";
    last by iApply big_opL_own_1.
  rewrite -big_opL_auth_frag -auth_frag_op /=.
  move: (big_opL_op_prodR 0)=> /= HOpL. rewrite !HOpL=> /=.
  rewrite -!pair_op ucmra_unit_left_id.
  rewrite -big_opL_op_gset -big_opL_op_max_nat /=.
  rewrite max_nat_op_max Max.max_l.
  2: {
    clear. move: m n. elim=> /= [n|m' IHm n].
    lia.
    move: (IHm (S n)). lia.
  }
  apply auth_update_alloc, prod_local_update';
    last by apply max_nat_local_update=> /=; lia.
  eapply transitivity.
  apply (gset_disj_alloc_empty_local_update _ (set_seq n m)).
  by symmetry; simpl; apply set_seq_plus_disjoint.
  by rewrite /= union_comm_L -set_seq_plus_L.
Qed.

Lemma iterator_counter_at_least_implies_bound γ n m:
    iterator_counter_at_least γ n -∗
    own γ (iterator_auth_ra m) -∗
    ⌜(n <= m)%nat⌝.
Proof.
  iIntros "HLeast HAuth".
  by iDestruct (own_valid_2 with "HAuth HLeast")
    as %[[_ HValid%max_nat_included]%prod_included _]%auth_both_valid.
Qed.

Theorem iterator_increaseValueTo_spec γ (fℓ: loc) (n: nat):
  ⊢ <<< ∀ m, ▷ iterator_counter γ fℓ m >>>
    (increaseValueTo #fℓ #n) @ ⊤
  <<< ([∗ list] i ∈ seq m (n - m), iterator_issued γ i) ∗
      iterator_counter_at_least γ (max n m) ∗
      (⌜m >= n⌝ ∧ iterator_counter γ fℓ m ∨
       ⌜m < n⌝ ∧ iterator_counter γ fℓ n), RET #() >>>.
Proof.
  iIntros (Φ) "AU".
  awp_apply increaseValueTo_spec.
  iApply (aacc_aupd_commit with "AU"); first done.
  iIntros (m) "[Hfℓ >H●]". iAaccIntro with "Hfℓ".
  by iFrame "H●"; iIntros "$ !> $ !> //".
  iIntros "[[% Hfℓ]|[% Hfℓ]]"; (iSplitL; last by iIntros "!> $ !>").
  { replace (n - m) with 0 by lia. simpl.
    iMod (own_update with "H●") as "[H● $]".
    {
      apply auth_update_core_id=> /=; first by apply _.
      do 2 try (apply prod_included=> /=; split).
      - by rewrite gset_disj_included.
      - apply max_nat_included=> /=; lia.
    }
    iLeft. iFrame. iPureIntro. lia.
  }
  assert (∃ k, n = m + S k) as [k ->];
    first by apply nat_lt_sum; lia.
  rewrite Max.max_l; last by lia.
  replace (m + S k - m) with (S k) by lia.
  iMod (iterator_value_increase _ _ (S k) with "H●") as "[H● [$ $]]".
  iRight. iFrame. by iPureIntro; lia.
Qed.

Lemma iterator_counter_is_at_least γ n:
  own γ (iterator_auth_ra n) ==∗
  own γ (iterator_auth_ra n) ∗ iterator_counter_at_least γ n.
Proof.
  iIntros "H●". iMod (own_update with "H●") as "[$ $]"; last done.
  apply auth_update_core_id; first by apply _.
  rewrite prod_included /=. split.
  by apply ucmra_unit_least.
  apply max_nat_included; simpl; lia.
Qed.

Lemma iterator_issued_is_at_least γ n:
  iterator_issued γ n -∗ iterator_counter_at_least γ (S n).
Proof.
  iIntros "H". iApply (own_mono with "H"). apply auth_included; split=>//=.
  apply prod_included; split; first by apply ucmra_unit_least.
  apply max_nat_included. simpl. done.
Qed.

Theorem newIterator_spec co γa P p n:
  {{{ is_infinite_array_cutoff _ _ aspc NArray γa p n ∗
      [∗] replicate n P }}}
    newIterator p #n
  {{{ γ v, RET v; is_iterator co γa P γ v }}}.
Proof.
  iIntros (Φ) "[HCutoff HPs] HΦ". wp_lam. wp_pures. rewrite -wp_fupd.
  wp_alloc ℓ as "Hℓ". wp_pures.
  iMod (own_alloc (iterator_auth_ra n)) as (γ) "H●".
  { rewrite /iterator_auth_ra. apply auth_auth_valid. done. }
  iMod (inv_alloc N _ (∃ n, iterator_contents co γa P γ ℓ p n)
       with "[HPs Hℓ H● HCutoff]") as "#HInv".
  { iExists n. iFrame "H● Hℓ HPs". iExists n. iFrame "HCutoff".
    iIntros (id HL). lia. }
  iApply "HΦ". iExists _, _. by iFrame "HInv".
Qed.

Theorem iteratorStep_spec co γa P γ (v: val):
  {{{ is_infinite_array _ _ aspc NArray γa co ∗ is_iterator co γa P γ v ∗ P }}}
    iteratorStep array_interface v
  {{{ n ns s, RET (#n, s); ⌜ns ≥ n⌝ ∧ iterator_issued γ n ∗
      is_infinite_array_cell_pointer _ _ aspc NArray γa s ns ∗
      ∀ i : nat, ⌜n ≤ i ∧ i < ns⌝ -∗
               cell_is_cancelled _ _ aspc NArray γa i ∗
               ∃ ℓ, infinite_array_mapsto _ _ aspc NArray co γa i ℓ
  }}}.
Proof.
  iIntros (Φ) "(#HArr & #HIter & HP) HΦ".
  iDestruct "HIter" as (cℓ p) "[% HInv]". simplify_eq.
  wp_lam. wp_pures. wp_bind (cutoffGetPointer _ _).
  awp_apply cutoffGetPointer_spec without "HP HΦ".
  iInv "HInv" as (start) "([Hfℓ >H●] & HPs & HSegment)".
  iDestruct "HSegment" as (start_id) "[#HCancelled HCutoff]".
  iAaccIntro with "HCutoff".
  {
    iIntros "HCutoff !>". iSplitL; last done. iExists _. iFrame.
    iExists start_id. by iFrame "HCancelled HCutoff".
  }
  iMod (iterator_counter_is_at_least with "H●") as "[H● #HAtLeast]".
  iIntros (cutoff) "[HCutoff #HReading]". iSplitL.
  { iExists _. iFrame. iExists start_id. by iFrame. }
  iIntros "!> [HP HΦ]". wp_pures. wp_bind (FAA _ _).

  iInv "HInv" as (start') "([Hfℓ H●] & HPs & HSeg)" "HClose".
  iDestruct (iterator_counter_at_least_implies_bound with "HAtLeast H●")
    as "#>%".
  wp_faa.
  iMod (iterator_value_increase _ _ 1 with "H●") as "[H● [#HAtLeast' [H◯ _]]]".
  rewrite -Nat2Z.inj_add Nat.add_1_r.
  iMod ("HClose" with "[-H◯ HΦ]") as "_".
  {
    iExists _. iFrame "H● Hfℓ HP HPs".
    iDestruct "HSeg" as (?) "[HCanc HCutoff]".
    iExists _. iFrame "HCutoff".
    iIntros (id' HLe). iApply "HCanc". iPureIntro. lia.
  }
  iModIntro. wp_pures.

  awp_apply (findCellAndMoveForward_spec with "HArr HReading")
            without "HΦ H◯".
  iInv "HInv" as (start'') "([Hfℓ H●] & HPs & HSegment)".
  iDestruct (iterator_counter_at_least_implies_bound with "HAtLeast' H●")
    as "#>%".
  iDestruct "HSegment" as (start_id'') "[#HCancelled'' HCutoff]".
  iAaccIntro with "HCutoff".
  {
    iIntros "HCutoff !>". iSplitL; last done. iExists _. iFrame.
    iExists _. by iFrame "HCutoff".
  }
  iIntros (seg segId) "(#HCellPointer & % & #HCancelled''' & HCutoff)".
  iAssert (∀ i, ⌜start' ≤ i < segId⌝ -∗ cell_is_cancelled _ _ aspc NArray γa i
          ∗ ∃ ℓ, infinite_array_mapsto _ _ aspc NArray co γa i ℓ)%I
    with "[]" as "#HCancelledSegId".
  {
    iIntros (id' HId').
    destruct (decide (id' < start_id)).
    by iApply "HCancelled"; iPureIntro; lia.
    by iApply "HCancelled'''"; iPureIntro; lia.
  }
  iDestruct "HCutoff" as (i' Hi') "HCutoff".
  iSplitL.
  - iExists _. iFrame "Hfℓ H● HPs".
    iExists _. iFrame "HCutoff".
    iIntros "!> !>" (id' HId').
    (* Was the cutoff even moved at all? *)
    destruct (decide (segId ≤ start_id'')%nat) as [HSegIdLeSId''|HSegIdGtSId''];
      [iApply "HCancelled''"|iApply "HCancelledSegId"].
    all: iPureIntro; lia.
  - iModIntro. iIntros "[HΦ HIssued]". wp_pures. iApply "HΦ".
    iFrame "HIssued HCancelledSegId HCellPointer". iPureIntro. lia.
Qed.

Theorem iteratorStepOrIncreaseCounter_spec
        (shouldAdjust: bool) co γa P γ (v: val):
  {{{ is_infinite_array _ _ aspc NArray γa co ∗ is_iterator co γa P γ v ∗ P ∗
      if shouldAdjust
      then make_laterable (∀ l start finish,
      (∀ i, ⌜start ≤ i < finish⌝ -∗ cell_is_cancelled _ _ aspc NArray γa i ∗
                (∃ ℓ, infinite_array_mapsto _ _ aspc NArray co γa i ℓ)) -∗
      ▷ [∗] replicate (S start) P -∗
      ([∗ list] i ∈ l, ⌜start ≤ i < finish⌝ ∗ iterator_issued γ i)
        ={⊤ ∖ ↑N}=∗ ▷ [∗] replicate ((S start) + length l) P) else True
  }}}
    iteratorStepOrIncreaseCounter array_interface #shouldAdjust v
  {{{ v, RET v; ⌜v = NONEV⌝ ∗
                (if shouldAdjust then P
                 else ∃ i, cell_is_cancelled _ _ aspc NArray γa i ∗
                           (∃ ℓ, infinite_array_mapsto _ _ aspc NArray co γa i ℓ) ∗
                           iterator_issued γ i) ∨
                ∃ ns s, ⌜v = SOMEV s⌝ ∧ iterator_issued γ ns ∗
                        is_infinite_array_cell_pointer _ _ aspc NArray γa s ns
  }}}.
Proof.
  iIntros (Φ) "(#HArr & #HIter & HP & HPs) HΦ".
  iDestruct "HIter" as (cℓ p) "[% HInv]". simplify_eq.
  wp_lam. wp_pures. wp_bind (iteratorStep _ _).
  iApply (iteratorStep_spec with "[HP]").
  {
    iFrame "HArr". iSplitR.
    - iExists _, _. by iFrame "HInv".
    - done.
  }
  iIntros (n ns s) "!> (% & HIssued & #HCellPointer & #HCancelled)". wp_pures.
  wp_apply (cellPointerId_spec with "[$]"). iIntros "_". wp_pures.
  destruct (decide (ns = n)) as [->|HNeq].
  - rewrite bool_decide_true //. wp_pures.
    iApply "HΦ". iRight. iExists _, _. iSplitR; first done.
    by iFrame.
  - rewrite bool_decide_false; last (case; lia). wp_pures.
    destruct shouldAdjust; wp_pures.
    2: {
      iApply "HΦ". iLeft. iSplitR; first done. iExists _.
      iFrame. iApply "HCancelled". iPureIntro. lia.
    }
    wp_apply (cellPointerId_spec with "[$]"). iIntros "_".
    wp_bind (increaseValueTo _ _).
    awp_apply iterator_increaseValueTo_spec without "HΦ".
    iInv "HInv" as (start) "(HCounter & HPs' & HSegment)".
    iAssert (▷ ⌜start > n⌝)%I with "[HIssued HCounter]" as "#>%".
    { iDestruct "HCounter" as "[_ H●]".
      iApply (iterator_counter_at_least_implies_bound
                with "[HIssued] H●").
      iApply (own_mono with "HIssued").
      rewrite auth_included /= prod_included /= max_nat_included /=.
      repeat split; eauto. apply ucmra_unit_least.
    }
    iAaccIntro with "HCounter".
    { iIntros "HCounter !>". iFrame "HIssued HPs". iExists _.
      iFrame. }
    iIntros "(HIssued' & _ & HCounter)".
    iDestruct (make_laterable_elim with "HPs") as "HPs".
    assert (∃ c, start = S n + c) as [c ->]. by apply nat_le_sum; lia.
    rewrite replicate_plus big_sepL_app.
    iDestruct "HPs'" as "[HPs' HPs'']".
    iSpecialize ("HPs" $! ([n] ++ seq (S n + c) (ns - (S n + c))) n
                   with "[] HPs'")=> /=.
    { iIntros (i Hi). iApply "HCancelled". iPureIntro. apply Hi. }
    iMod ("HPs" with "[HIssued HIssued']") as "HPs".
    { iFrame. iSplitR; first by iPureIntro; lia.
      iApply (big_sepL_impl with "HIssued'"). iIntros "!>" (? ? HEl) "$".
      iPureIntro. move: HEl. rewrite lookup_seq. case=> ->. lia. }
    iDestruct "HPs" as "[HP HPs]".
    rewrite seq_length. iCombine "HPs HPs''" as "HPs".
    iDestruct "HCounter" as "[[% HCounter]|[% HCounter]]".
    * iSplitL "HPs HSegment HCounter".
      { iExists _. iFrame "HSegment HCounter". simpl.
        rewrite !replicate_plus !big_sepL_app.
        by iDestruct "HPs" as "[($ & $ & _) $]". }
      iIntros "!> HΦ". wp_pures. iApply "HΦ". iLeft. by iFrame.
    * iSplitR "HP".
      { iExists _. iFrame "HCounter".
        iModIntro. iModIntro.
        iSplitL "HPs".
        - assert (∃ k, ns = (S n + c) + S k) as [k ->].
          by apply nat_lt_sum; lia.
          replace (_ + S k - _) with (S k) by lia.
          rewrite !replicate_plus !big_sepL_app.
          iDestruct "HPs" as "[[$ ($ & $ & $)] $]".
        - iDestruct "HSegment" as (id) "[#HCancelled' HCutoff]".
          iExists _; iFrame "HCutoff".
          iIntros (? ?). iApply "HCancelled'". iPureIntro. lia.
      }
      iIntros "!> HΦ". wp_pures. iApply "HΦ". iLeft. by iFrame.
Qed.

Lemma access_iterator_resources E R co γa γd d i:
  ↑N ⊆ E ->
  is_iterator co γa R γd d -∗
  iterator_counter_at_least γd i
  ={E,E∖↑N}=∗ ▷ ([∗] replicate i R)
              ∗ ((▷ [∗] replicate i R) ={E∖↑N, E}=∗ True).
Proof.
  iIntros (HSets) "#HIsIter HCounterValue".
  iDestruct "HIsIter" as (cℓ p) "[-> HIsIter]".
  iInv N as (n) "(HCounter & HResource & HCutoff)" "HClose".
  iModIntro. rewrite /iterator_counter.
  iDestruct "HCounter" as "[Hcℓ H●]".
  iDestruct (own_valid_2 with "H● [$]") as "#HPure".
  destruct (decide (i ≤ n)) as [HValid|HContra].
  - apply nat_le_sum in HValid. destruct HValid as [z ->].
    rewrite replicate_plus big_sepL_app.
    iDestruct "HResource" as "[$ HResource]".
    iIntros "HResource'". iMod ("HClose" with "[-]"); last done.
    iExists (i + z). iFrame. rewrite replicate_plus big_sepL_app. iFrame.
  - iSplitR.
    * iDestruct "HPure" as ">HPure".
      iDestruct "HPure"
        as %[[_ HValid%max_nat_included]%prod_included _]%auth_both_valid.
      simpl in *. lia.
    * iIntros "_". iDestruct "HPure" as ">HPure".
      iDestruct "HPure"
        as %[[_ HValid%max_nat_included]%prod_included _]%auth_both_valid.
      simpl in *. lia.
Qed.

End proof.

Typeclasses Opaque iterator_counter iterator_counter_at_least
            iterator_contents is_iterator.
