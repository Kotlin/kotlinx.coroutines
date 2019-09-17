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
       if: ! "tmp" < "val"
       then if: CAS "loc" ! "tmp" "val" then #()
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

Variable segment_size: positive.
Variable ap: @infinite_array_parameters Σ.

Variable cell_is_processed: nat -> iProp Σ.
Variable cell_is_processed_persistent:
  forall n, Persistent (cell_is_processed n).
Existing Instance cell_is_processed_persistent.

Context `{iArrayG Σ}.

Notation algebra := (authR (prodUR (gset_disjUR nat) mnatUR)).

Class iteratorG Σ := IIteratorG { iterator_inG :> inG Σ algebra }.
Definition iteratorΣ : gFunctors := #[GFunctor algebra].
Instance subG_iteratorΣ {Σ} : subG iteratorΣ Σ -> iteratorG Σ.
Proof. solve_inG. Qed.

Context `{iteratorG Σ}.

Notation iProp := (iProp Σ).

Definition iterator_counter γ fℓ (n: nat): iProp :=
  (fℓ ↦ #n ∗ own γ (● (GSet (set_seq 0 n), n: mnatUR)))%I.

Definition iterator_counter_at_least γ (n: nat): iProp :=
  own γ (◯ (ε, n: mnatUR)).

Lemma iterator_counter_at_least_persistent γ n:
  Persistent (iterator_counter_at_least γ n).
Proof. apply _. Qed.

Definition iterator_points_to γa γ fℓ ℓ n: iProp :=
  (iterator_counter γ fℓ n ∗
                    ∃ (id: nat), ⌜(id * Pos.to_nat segment_size <= n)%nat⌝ ∗
                                  (∃ (ℓ': loc), segment_location γa id ℓ'
                                                                 ∗ ℓ ↦ #ℓ'))%I.

Definition is_iterator γa γ fℓ ℓ: iProp :=
  (∃ n, iterator_points_to γa γ fℓ ℓ n)%I.

Definition iterator_issued γ n :=
  own γ (◯ (GSet {[ n ]}, S n: mnatUR)).

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
  cell_init segment_size ap ∅ -∗
  <<< ▷ is_infinite_array segment_size ap γa ∗ is_iterator γa γ fℓ ℓ >>>
     (iterator_step segment_size) #ℓ #fℓ @ ⊤
  <<< ∃ (ix: nat) (sℓ: loc),
    ▷ is_infinite_array segment_size ap γa ∗ is_iterator γa γ fℓ ℓ ∗
    ∃ (id: nat) (n: nat),
    ⌜(ix < Pos.to_nat segment_size)%nat⌝ ∗
    segment_location γa id sℓ ∗
    iterator_issued γ n ∗
    (∃ ℓ, ▷ p_cell_invariant ap γa n ℓ ∗ array_mapsto segment_size γa n ℓ) ∗
    (⌜n = (id * Pos.to_nat segment_size + ix)%nat⌝ ∨
      cell_is_cancelled segment_size γa n), RET (#sℓ, #ix) >>>.
Proof.
  iIntros "#HCellInit".
  iIntros (Φ) "AU". wp_lam. wp_pures.

  wp_bind (!_)%E.
  iMod "AU" as "[[HInfArr HIsIter] [HClose _]]".
  iDestruct "HIsIter" as (n') "([Hfℓ HAuth] & HSeg)".
  iDestruct "HSeg" as (? ? ?) "(#HSegLoc & Hℓ)".
  wp_load.
  iMod (own_update with "HAuth") as "[HAuth HSent]". {
    apply auth_update_core_id with (b := (ε, n': mnatUR)).
    apply _.
    rewrite prod_included /=; split; rewrite //.
    apply gset_disj_included. done.
  }
  iMod ("HClose" with "[- HSent]") as "AU". {
    rewrite /is_iterator. repeat (iFrame; iExists _).
    iSplitR. 2: by iExists _; iFrame. done.
  }
  iModIntro. wp_pures.

  wp_bind (FAA _ _)%E.
  iMod "AU" as "[[HInfArr HIsIter] [HClose _]]".
  iDestruct "HIsIter" as (n) "([Hfℓ HAuth] & HSeg)".
  iDestruct "HSeg" as (? ? ?) "(#HSegLoc' & Hℓ)".
  destruct (le_lt_dec n' n).
  2: {
    iDestruct (own_valid_2 with "HAuth HSent") as %HContra.
    exfalso. move: HContra.
    rewrite auth_both_valid prod_included mnat_included /=.
    lia.
  }
  wp_faa.
  iMod (own_update with "HAuth") as "[HAuth HFrag]".
  { apply auth_update_alloc. apply prod_local_update'.
    eapply (gset_disj_alloc_empty_local_update _ {[ n ]}).
    apply (set_seq_S_end_disjoint 0).
    apply mnat_local_update. Existential 2 := (S n). lia.
  }
  rewrite -(set_seq_S_end_union_L 0).
  iMod ("HClose" with "[-HFrag HSent]") as "AU". {
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

  iExists (n `mod` Pos.to_nat segment_size)%nat, _. iFrame.
  iSplitL.
  2: {
    iIntros "!> HΦ !>". wp_pures.
    destruct (Pos.to_nat segment_size) as [|o'] eqn:HC.
    exfalso; lia. rewrite rem_of_nat; done. }
  iExists _, _. iFrame. iFrame "HSegLoc''".
  iSplitR. iPureIntro; apply Nat.mod_upper_bound; lia.
  iSplitL "HSegInv".
  { iDestruct (cell_invariant_by_segment_invariant with "HSegInv")
      as (cℓ) "[HCellInv >HArrMapsto]".
    by eapply Nat.mod_upper_bound; lia.
    iExists _. iModIntro.
    rewrite /array_mapsto /ias_cell_info_view.
    iFrame "HArrMapsto".
    rewrite Nat.mul_comm -Nat.div_mod. done. lia. }

  iDestruct "HFindSegRet" as "[[% ->]|(% & % & #HCanc)]".

  {
    assert (a = n `div` Pos.to_nat segment_size)%nat as ->. {
      assert (a * Pos.to_nat segment_size <= n)%nat as HC by lia.
      rewrite (Nat.div_mod n (Pos.to_nat segment_size)) in HC.
      2: lia.
      remember (n `div` Pos.to_nat segment_size)%nat as k.
      remember (Pos.to_nat segment_size) as m.
      assert (m > 0)%nat as MGt0 by lia.
      assert (k ≤ a)%nat as HC' by lia.
      revert MGt0 HC HC'. clear. intros.
      rewrite Nat.mul_comm in HC.
      assert ((a - k) * m <= n `mod` m)%nat by (rewrite Nat.mul_sub_distr_r; lia).
      assert (n `mod` m < m)%nat by (apply Nat.mod_upper_bound; lia).
      assert ((a - k) * m < m)%nat as HC'' by lia.
      destruct (a - k)%nat eqn:E; simpl in *; lia.
    }

    iLeft. iPureIntro.
    rewrite Nat.mul_comm -Nat.div_mod /= //.
    lia.
  }

  destruct (decide (a = n `div` Pos.to_nat segment_size)%nat); subst.
  {
    iLeft. iPureIntro.
    rewrite Nat.mul_comm -Nat.div_mod /= //.
    lia.
  }

  iRight. iModIntro.

  iDestruct (segments_cancelled__cells_cancelled with "HCanc") as "HCanc'".
  iApply (big_sepL_lookup _ _ (n `mod` Pos.to_nat segment_size)%nat with "HCanc'").
  rewrite seq_lookup.
  - rewrite Nat.mul_comm -Nat.div_mod. done. lia.
  - apply Nat.lt_le_trans with (m := (1 * Pos.to_nat segment_size)%nat).
    by rewrite Nat.mul_1_l; apply Nat.mod_upper_bound; lia.
    by apply mult_le_compat_r; lia.
Qed.

Theorem increase_value_to_spec γ (fℓ: loc) (n: nat):
  <<< ∀ m, iterator_counter γ fℓ m >>>
    (increase_value_to #fℓ #n) @ ⊤
  <<< own γ (◯ (GSet (set_seq m (n-m)%nat), n: mnatUR)) ∗
      (⌜m >= n⌝ ∧ iterator_counter γ fℓ m ∨
       ⌜m < n⌝ ∧ iterator_counter γ fℓ n), RET #() >>>.
Proof.
  iIntros (Φ) "AU". wp_lam. wp_pures. wp_bind (!_)%E.
  iMod "AU" as (m) "[[Hfℓ HAuth] HClose]". wp_load.
  destruct (decide (m < n)) eqn:E.

  2: {
    iMod (own_update with "HAuth") as "[HAuth HOk]".
    { apply auth_update_core_id with (b := (ε, n: mnatUR)).
      by apply _.
      rewrite prod_included. split; simpl.
      by apply gset_disj_included.
      apply mnat_included. lia.
    }
    iMod ("HClose" with "[-]") as "HΦ".
    { replace (n - m)%nat with O by lia. simpl.
      iFrame "HOk". iLeft. iSplitR. by iPureIntro; lia. iFrame. }
    iModIntro. wp_alloc tℓ as "Htℓ". wp_pures. wp_load. wp_pures.
    rewrite bool_decide_decide E. wp_pures. done.
  }

  iDestruct "HClose" as "[HClose _]"; iMod ("HClose" with "[$]") as "AU".
  iModIntro. wp_alloc tℓ as "Htℓ". wp_pures. wp_load. wp_pures.
  rewrite bool_decide_decide E. wp_pures. clear E.

  iLöb as "IH" forall (m l).

  wp_load. wp_bind (CmpXchg _ _ _). iMod "AU" as (m') "[[Hfℓ HAuth] HClose]".
  destruct (decide (m' = m)); subst.
  {
    wp_cmpxchg_suc.
    iMod (own_update with "HAuth") as "[HAuth HOk]".
    { apply auth_update_alloc. apply prod_local_update'.
      - apply (gset_disj_alloc_empty_local_update
                 _ (set_seq (O + m)%nat (n - m)%nat)).
        symmetry. apply set_seq_plus_disjoint.
      - apply mnat_local_update.
        assert (m <= n)%nat as HP by lia. apply HP.
    }
    iMod ("HClose" with "[-Htℓ]") as "HΦ".
    { simpl. iFrame "HOk".
      rewrite union_comm_L -set_seq_plus_L.
      iRight.
      replace (m + (n - m))%nat with n by lia.
      iFrame.
      by iPureIntro. }
    iModIntro. by wp_pures.
  }
  {
    wp_cmpxchg_fail.
    { case. intros HContra. apply Nat2Z.inj in HContra. contradiction. }
    iDestruct "HClose" as "[HClose _]". iMod ("HClose" with "[$]") as "AU".

    iModIntro. wp_pures. wp_bind (!_)%E.
    iMod "AU" as (m'') "[[Hfℓ HAuth] HClose]". wp_load.

    destruct (decide (m'' < n)) eqn:E.

    2: {
      iMod (own_update with "HAuth") as "[HAuth HOk]".
      { apply auth_update_core_id with (b := (ε, n: mnatUR)).
        by apply _.
        rewrite prod_included. split; simpl.
        by apply gset_disj_included.
        apply mnat_included. lia.
      }
      iMod ("HClose" with "[-Htℓ]") as "HΦ".
      { replace (n - m'')%nat with O by lia. simpl.
        iFrame "HOk". iLeft. iSplitR. by iPureIntro; lia. iFrame. }
      iModIntro. wp_store. wp_pures. wp_load. wp_pures.
      rewrite bool_decide_decide E. wp_pures. done.
    }

    iDestruct "HClose" as "[HClose _]". iMod ("HClose" with "[$]") as "AU".
    iModIntro. wp_store. wp_pures. wp_load. wp_pures.
    rewrite bool_decide_decide E. wp_pures.

    by iApply ("IH" with "[%] AU Htℓ").
  }
Qed.

End proof.
