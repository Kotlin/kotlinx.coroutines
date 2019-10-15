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

Theorem iterator_issued_timeless γ n: Timeless (iterator_issued γ n).
Proof. apply _. Qed.

Theorem iterator_issued_exclusive γ n:
  iterator_issued γ n -∗ iterator_issued γ n -∗ False.
Proof.
  iIntros "HIss HIss'".
  iDestruct (own_valid_2 with "HIss HIss'") as %HContra.
  exfalso. revert HContra. clear. rewrite -auth_frag_op -pair_op.
  case; simpl. rewrite gset_disj_valid_op. rewrite disjoint_singleton_l.
  case. rewrite elem_of_singleton. done.
Qed.

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

Lemma iterator_value_increase (n m: nat):
  ● (GSet (set_seq 0 n), n: mnatUR) ~~>
  ● (GSet (set_seq 0 (n + m)%nat), (n + m)%nat: mnatUR) ⋅
  ◯ (GSet (set_seq n m), (n + m)%nat: mnatUR).
Proof.
  apply auth_update_alloc, prod_local_update'.
  2: by apply mnat_local_update; lia.
  eapply transitivity.
  apply (gset_disj_alloc_empty_local_update
            _ (set_seq (O + n)%nat m)).
  by symmetry; simpl; apply set_seq_plus_disjoint.
  by rewrite /= union_comm_L -set_seq_plus_L.
Qed.

Theorem iterator_value_faa γa γ (fℓ ℓ: loc) (m: nat):
  <<< ∀ (n: nat), iterator_points_to γa γ fℓ ℓ n >>>
    FAA #fℓ #m @ ⊤
  <<< iterator_points_to γa γ fℓ ℓ (n+m)%nat ∗
    own γ (◯ (GSet (set_seq n m), (n + m)%nat: mnatUR)), RET #n >>>.
Proof.
  iIntros (Φ) "AU".

  iMod "AU" as (n) "[([Hfℓ HAuth] & HSeg) [_ HClose]]".
  iDestruct "HSeg" as (? ? ?) "(#HSegLoc' & Hℓ)".
  wp_faa.
  iMod (own_update with "HAuth") as "[HAuth HFrag]".
  by apply iterator_value_increase.
  iApply "HClose".
  iFrame "HAuth". rewrite Nat2Z.inj_add. iFrame "Hfℓ HFrag".
  iExists _. iSplitR.
  2: iExists _; by iFrame "Hℓ".
  iPureIntro. lia.
Qed.

Lemma iterator_points_to_at_least γ ℓ n m:
    iterator_counter_at_least γ n -∗
    iterator_counter γ ℓ m -∗
    ⌜(n <= m)%nat⌝.
Proof.
  iIntros "HLeast [_ HAuth]".
  by iDestruct (own_valid_2 with "HAuth HLeast")
    as %[[_ HValid%mnat_included]%prod_included _]%auth_both_valid.
Qed.

Lemma find_segment_id_bound a p n n':
  (p > 0)%nat -> (a * p <= n')%nat -> (n' <= n)%nat ->
  (n `div` p <= a)%nat -> (a = n `div` p)%nat.
Proof.
  intros.
  assert (a * p <= n)%nat as HC by lia.
  rewrite (Nat.div_mod n p) in HC.
  2: lia.
  remember (n `div` p)%nat as k.
  assert (k ≤ a)%nat as HC' by lia.
  rewrite Nat.mul_comm in HC.
  assert ((a - k) * p <= n `mod` p)%nat by (rewrite Nat.mul_sub_distr_r; lia).
  assert (n `mod` p < p)%nat; first by (apply Nat.mod_upper_bound; lia).
  assert ((a - k) * p < p)%nat as HC'' by lia.
  destruct (a - k)%nat eqn:E; simpl in *; lia.
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

  awp_apply (iterator_value_faa). iApply (aacc_aupd_abort with "AU"); first done.
  iIntros "[HInfArray HIsIter]".
  iDestruct "HIsIter" as (n) "HIsIter".
  iDestruct (iterator_points_to_at_least with "HSent [HIsIter]") as %Hn'LNp1.
  by iDestruct "HIsIter" as "[$ _]".
  iAaccIntro with "HIsIter".
  {
    iIntros "HIsIter !>". iSplitR "HSent".
    iFrame "HInfArray"; iExists _; iFrame "HIsIter".
    iIntros "$". iFrame "HSent". done.
  }
  iIntros "[HIsIter HPerms]".
  iFrame "HInfArray". iSplitL "HIsIter".
  { iExists _. auto. }
  iIntros "!> AU !>". wp_pures.

  wp_bind (find_segment _ _ _).
  replace (Z.of_nat n `quot` Z.of_nat (Pos.to_nat segment_size)) with
      (Z.of_nat (n `div` Pos.to_nat segment_size)%nat).
  2: by rewrite quot_of_nat.

  awp_apply find_segment_spec; try done.
  iApply (aacc_aupd_commit with "AU"); first done.
  iIntros "[HInfArr HIsIter]".
  iAaccIntro with "HInfArr".
  { iIntros "HInfArr". iFrame. eauto. }

  iIntros (? ?) "(HInfArr & HSegInv & #HSegLoc'' & #HFindSegRet)".

  iExists (n `mod` Pos.to_nat segment_size)%nat, _. iFrame.
  iSplitL.
  2: {
    iIntros "!> HΦ !>". wp_pures.
    destruct (Pos.to_nat segment_size) as [|o'] eqn:HC.
    exfalso; lia. rewrite rem_of_nat; done. }
  iExists _, _. iFrame "HSegLoc''".
  iSplitR. iPureIntro; apply Nat.mod_upper_bound; lia.
  iSplitL "HPerms".
  by rewrite /= union_empty_r_L Nat.add_1_r /iterator_issued.
  iSplitL "HSegInv".
  {
    iAssert (⌜seq O (S a) !! _ =
             Some (O + n `div` Pos.to_nat segment_size)%nat⌝)%I as %HEl.
    {
      iDestruct "HFindSegRet" as "[[% ->]|(% & % & #HCanc)]";
        iPureIntro; apply seq_lookup; lia.
    }
    iDestruct (big_sepL_lookup with "HSegInv") as "HSegInv"; first done.
    iDestruct (cell_invariant_by_segment_invariant with "HSegInv")
      as (cℓ) "[HCellInv >HArrMapsto]".
    by eapply Nat.mod_upper_bound; lia.
    iExists _. iModIntro.
    rewrite /array_mapsto /ias_cell_info_view.
    iFrame "HArrMapsto".
    rewrite Nat.mul_comm -Nat.div_mod. done. lia. }

  iDestruct "HFindSegRet" as "[[% ->]|(% & % & #HCanc)]".

  {
    assert (a = n `div` Pos.to_nat segment_size)%nat as ->. {
      eapply find_segment_id_bound; try lia. done.
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
    assert (exists k, n = (m + k)%nat) as [? ->].
    by rewrite -nat_le_sum; lia.
    iMod (own_update with "HAuth") as "[HAuth HOk]".
    by apply iterator_value_increase.
    iMod ("HClose" with "[-Htℓ]") as "HΦ".
    { simpl. replace (m + x - m)%nat with x by lia. iFrame "HOk".
      iRight. iFrame. by iPureIntro. }
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
