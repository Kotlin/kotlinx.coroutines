From iris.heap_lang Require Import proofmode notation lang.
Require Import SegmentQueue.lib.infinite_array.infinite_array_impl.

Section impl.

Variable segment_size: positive.

Definition iterator_step: val :=
  (λ: "seg" "idx",
   let: "segv" := !"seg" in
   let: "p" := FAA "idx" #1%nat in
   let: "s" := (find_segment segment_size)
                 "segv" ("p" `quot` #(Pos.to_nat segment_size)) in
   ("s", "p" `rem` #(Pos.to_nat segment_size))).

Definition increase_value_to: val :=
  (λ: "loc" "val",
     let: "tmp" := ref !"loc" in
    (rec: "loop" <> :=
       if: "tmp" < "val"
       then if: CAS "loc" "tmp" "val" then #()
            else "tmp" <- !"loc" ;; "loop" #()
       else #()) #()
  ).

Definition iterator_step_skipping_cancelled: val :=
  (rec: "loop" "seg" "idx" :=
     let: "segv" := !"seg" in
     let: "p" := FAA "idx" #1%nat in
     let: "id" := ("p" `quot` #(Pos.to_nat segment_size)) in
     let: "s" := (find_segment segment_size) "segv" "id" in
     if: segment_id "s" = "id" then ("s", "p" `rem` #(Pos.to_nat segment_size))
     else
       increase_value_to "idx" (segment_id "s" * #(Pos.to_nat segment_size)) ;;
       "loop" "seg" "idx"
  ).

End impl.

From iris.program_logic Require Import atomic.
From iris.algebra Require Import cmra auth list agree csum excl gset frac.

Section proof.

Context `{heapG Σ}.

Variable ap: @infinite_array_parameters Σ.
Let segment_size := p_segment_size ap.

Variable cell_is_processed: nat -> iProp Σ.
Variable cell_is_processed_persistent:
  forall n, Persistent (cell_is_processed n).
Existing Instance cell_is_processed_persistent.

Context `{iArrayG Σ}.

Notation algebra := (authR (gset_disjUR nat)).

Class iteratorG Σ := IIteratorG { iterator_inG :> inG Σ algebra }.
Definition iteratorΣ : gFunctors := #[GFunctor algebra].
Instance subG_iteratorΣ {Σ} : subG iteratorΣ Σ -> iteratorG Σ.
Proof. solve_inG. Qed.

Context `{iteratorG Σ}.

Notation iProp := (iProp Σ).

Definition is_iterator γa γ fℓ ℓ: iProp :=
  (∃ (n: nat), fℓ ↦ #n ∗ own γ (● (GSet (set_seq 0 n))) ∗
                  ∃ (id: nat), ⌜(id * Pos.to_nat segment_size <= n)%nat⌝ ∗
                                (∃ (ℓ': loc), segment_location γa id ℓ'
                                                               ∗ ℓ ↦ #ℓ'))%I.

Lemma quot_of_nat n m:
  Z.of_nat n `quot` Z.of_nat m = Z.of_nat (n `div` m).
Proof.
  destruct m. destruct n; done.
  rewrite Z2Nat_inj_div; apply Z.quot_div_nonneg; lia.
Qed.

Lemma rem_of_nat n m:
  Z.of_nat n `rem` Z.of_nat (S m) = Z.of_nat (n `mod` S m).
Proof.
  rewrite Z2Nat_inj_mod; apply Z.rem_mod_nonneg; lia.
Qed.

Theorem iterator_step_spec γa γ (ℓ fℓ: loc):
  cell_init ap -∗
  <<< ▷ is_infinite_array ap γa ∗ is_iterator γa γ fℓ ℓ >>>
    (iterator_step segment_size) #ℓ #fℓ @ ⊤
    <<< ∃ (ix: nat) (sℓ: loc),
      ▷ is_infinite_array ap γa ∗ is_iterator γa γ fℓ ℓ ∗
      ∃ (id: nat) (n: nat),
      ⌜(ix < Pos.to_nat segment_size)%nat⌝ ∗
      ⌜(id * Pos.to_nat segment_size <= n)%nat⌝ ∗
      segment_location γa id sℓ ∗
      own γ (◯ (GSet {[ n ]})) ∗
      (∃ ℓ, p_cell_invariant ap γa (id * Pos.to_nat segment_size + ix) ℓ) ∗
      (⌜n = (id * Pos.to_nat segment_size + ix)%nat⌝ ∨ cell_is_cancelled' γa id ix),
           RET (#sℓ, #ix) >>>.
Proof.
  iIntros "#HCellInit".
  iIntros (Φ) "AU". wp_lam. wp_pures.

  wp_bind (!_)%E.
  iMod "AU" as "[[HInfArr HIsIter] [HClose _]]".
  iDestruct "HIsIter" as (?) "(Hfℓ & HAuth & HSeg)".
  iDestruct "HSeg" as (? ? ?) "(#HSegLoc & Hℓ)".
  wp_load.
  iMod ("HClose" with "[-]") as "AU". {
    rewrite /is_iterator. repeat (iFrame; iExists _).
    iSplitR. 2: by iExists _; iFrame. done.
  }
  iModIntro. wp_pures.

  wp_bind (FAA _ _)%E.
  iMod "AU" as "[[HInfArr HIsIter] [HClose _]]".
  iDestruct "HIsIter" as (n) "(Hfℓ & HAuth & HSeg)".
  iDestruct "HSeg" as (? ? ?) "(#HSegLoc' & Hℓ)".
  wp_faa.
  iMod (own_update with "HAuth") as "[HAuth HFrag]".
  { apply auth_update_alloc.
    eapply (gset_disj_alloc_empty_local_update _ {[ n ]}).
    apply (set_seq_S_end_disjoint 0). }
  rewrite -(set_seq_S_end_union_L 0).
  iMod ("HClose" with "[-]") as "AU". {
    rewrite /is_iterator. iFrame; repeat (iExists _; iFrame).
    replace (n + 1%nat) with (Z.of_nat (S n)) by lia. iFrame.
    iExists _; iFrame.
    iSplitR. 2: by iExists _; iFrame. iPureIntro. lia.
  }
  iModIntro. wp_pures.

  wp_bind (find_segment _ _ _).
  replace (Z.of_nat n `quot` Z.of_nat (Pos.to_nat segment_size)) with
      (Z.of_nat (n `div` Pos.to_nat segment_size)%nat).
  2: by rewrite quot_of_nat.

  awp_apply find_segment_spec; try done.
  iApply (aacc_aupd_commit with "AU"); first done.
  iIntros "[HInfArr HIsIter]".
  iAaccIntro with "HInfArr".
  { iIntros "HInfArr". iFrame. eauto. }

  iIntros (? ?) "(HInfArr & HSegInv & #HSegLoc'' & HFindSegRet)".

  iDestruct "HFindSegRet" as "[[% ->]|(% & % & #HCanc)]".

Abort.
