From iris.base_logic.lib Require Export invariants.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation lang.
From iris.program_logic Require Export weakestpre atomic.

Section getAndSetProof.

Context `{heapG} (N: namespace).

Definition getAndSetInner : val :=
  rec: "getAndSet" "p" "g" "l" "v" "o" :=
    let: "r" := Resolve (CmpXchg "l" "o" "v") "p" "g" in
    if: Snd "r"
    then "o"
    else "getAndSet" "p" "g" "l" "v" (Fst "r").

Definition getAndSet : val :=
  λ: "l" "v",
  let: "p" := NewProph in
  let: "g" := ref #() in
    getAndSetInner "p" "g" "l" "v" #0.

Theorem getAndSet_spec : forall (ℓ: loc) v, val_is_unboxed v ->
  inv N (∃ v, ℓ ↦{1/2} v ∧ ⌜val_is_unboxed v⌝) -∗
  <<< ∀ k, ℓ ↦{1/2} k >>>
    getAndSet #ℓ v @ ⊤ ∖ ↑N
  <<< ℓ ↦{1/2} v, RET k >>>.
Proof.
  iIntros (ℓ v v_unboxed) "#HInv".
  iIntros (Φ) "AU".
  wp_lam.
  wp_let.
  wp_bind NewProph.
  wp_apply wp_new_proph; auto.
  iIntros (pvs p) "HProph".
  remember #0 as o.
  assert (val_is_unboxed o) as o_unboxed by (subst; done).
  clear Heqo.
  wp_let.
  wp_bind (ref _)%E.
  wp_alloc lg_ghost as "Hghost".
  wp_let.
  iLöb as "IH" forall (o pvs o_unboxed).
  wp_rec.
  wp_pures.
  wp_bind (Resolve _ _ _)%E.
  iInv N as "Hℓ" "HClose".
  iDestruct "Hℓ" as (trueVal) ">[Hℓ %]".
  destruct pvs.
  - iMod "AU" as (k) "[HAU [_ HCloseAU]]".
    iDestruct (mapsto_combine with "HAU Hℓ") as "[Hℓ <-]".
    replace (1 / 2 + 1 / 2)%Qp with 1%Qp by (rewrite Qp_half_half; done).
    destruct (decide (o = k)); subst.
    * wp_apply (wp_resolve_cmpxchg_suc with "[HProph Hℓ]"); auto.
      + left; done.
      + iFrame.
      + iIntros "Hpvs'".
        iDestruct "Hpvs'" as (pvs') "[% _]".
        discriminate.
    * wp_apply (wp_resolve_cmpxchg_fail with "[HProph Hℓ]"); eauto with iFrame.
      + right; done.
      + iIntros "Hpvs'". iDestruct "Hpvs'" as (pvs') "[% _]".
        discriminate.
  - destruct (decide (p0 = ((o, #true)%V, #lg_ghost))).
    * subst.
      iMod "AU" as (k) "[HAU [_ HCloseAU]]".
      iDestruct (mapsto_combine with "HAU Hℓ") as "[Hℓ <-]".
      replace (1 / 2 + 1 / 2)%Qp with 1%Qp by (rewrite Qp_half_half; done).
      destruct (decide (o = k)); subst.
      2: {
        wp_apply (wp_resolve_cmpxchg_fail with "[HProph Hℓ]"); eauto with iFrame.
        + right; done.
        + iIntros "Hpvs'". iDestruct "Hpvs'" as (pvs') "[% _]".
          discriminate.
      }
      wp_apply (wp_resolve_cmpxchg_suc with "[HProph Hℓ]"); eauto with iFrame.
      { right; done. }
      iIntros "Hpvs'". iDestruct "Hpvs'" as (pvs') "[% [HProph Hℓ]]".
      replace (ℓ ↦ v)%I with (ℓ ↦{1/2 + 1/2} v)%I by (rewrite Qp_half_half; done).
      inversion H1; subst. clear H1.
      iDestruct "Hℓ" as "[Hℓ1 Hℓ2]".
      iMod ("HCloseAU" with "Hℓ1") as "HΦ".
      iModIntro.
      iMod ("HClose" with "[Hℓ2]") as "_"; first by (eauto with iFrame).
      iModIntro.
      wp_pures.
      auto.
    * destruct (decide (o = trueVal)).
      {
        iMod "AU" as (k) "[HAU [_ HCloseAU]]".
        iDestruct (mapsto_combine with "HAU Hℓ") as "[Hℓ <-]".
        replace (1 / 2 + 1 / 2)%Qp with 1%Qp by (rewrite Qp_half_half; done).
        wp_apply (wp_resolve_cmpxchg_suc with "[HProph Hℓ]"); eauto with iFrame.
        { right; done. }
        { subst; iFrame. }
        iIntros "Hpvs'". iDestruct "Hpvs'" as (pvs') "[% [HProph Hℓ]]".
        inversion H1.
        subst.
        contradiction.
      }
      wp_apply (wp_resolve_cmpxchg_fail with "[HProph Hℓ]"); eauto with iFrame.
      { right; done. }
      iIntros "Hpvs'". iDestruct "Hpvs'" as (pvs') "[% [HProph Hℓ]]".
      iMod ("HClose" with "[Hℓ]") as "_"; first by auto.
      iModIntro.
      wp_let.
      wp_proj.
      wp_if.
      wp_proj.
      iSpecialize ("IH" $! trueVal pvs' H0).
      clear.
      iSpecialize ("IH" with "AU HProph Hghost").
      wp_apply "IH".
Qed.

End getAndSetProof.
