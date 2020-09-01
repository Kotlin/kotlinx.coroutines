From iris.heap_lang Require Export notation.

Definition increaseValueTo: val :=
  rec: "loop" "loc" "val" :=
    let: "cur" := !"loc" in
    if: "val" ≤ "cur" then #()
    else if: CAS "loc" "cur" "val" then #()
         else "loop" "loc" "val".

From iris.program_logic Require Import atomic.
From iris.heap_lang Require Export proofmode.

Section proof.

Context `{heapG}.

Theorem increaseValueTo_spec (ℓ: loc) (n: Z):
  ⊢ <<< ∀ (m: Z), ▷ ℓ ↦ #m >>>
    increaseValueTo #ℓ #n @ ⊤
  <<< ⌜(m >= n)%Z⌝ ∧ ℓ ↦ #m ∨ ⌜(m < n)%Z⌝ ∧ ℓ ↦ #n, RET #() >>>.
Proof.
  iIntros (Φ) "AU". wp_lam. wp_pures. iLöb as "IH".
  wp_bind (!_)%E. iMod "AU" as (m) "[Hℓ HClose]".
  wp_load.
  destruct (decide (n <= m)%Z) as [HLe|HGt].
  - iDestruct "HClose" as "[_ HClose]".
    iMod ("HClose" with "[Hℓ]") as "HΦ".
    { iLeft. iFrame. iPureIntro. lia. }
    iModIntro. wp_pures. rewrite bool_decide_true; last lia.
    by wp_pures.
  - iDestruct "HClose" as "[HClose _]".
    iMod ("HClose" with "Hℓ") as "AU".
    iModIntro. wp_pures. rewrite bool_decide_false; last lia.
    wp_pures. wp_bind (CmpXchg _ _ _).
    iMod "AU" as (m') "[Hℓ HClose]".
    destruct (decide (m = m')) as [<-|HNeq].
    + wp_cmpxchg_suc.
      iDestruct "HClose" as "[_ HClose]".
      iMod ("HClose" with "[Hℓ]") as "HΦ".
      { iRight. iFrame. iPureIntro. lia. }
      iModIntro. by wp_pures.
    + wp_cmpxchg_fail.
      iDestruct "HClose" as "[HClose _]".
      iMod ("HClose" with "Hℓ") as "AU".
      iModIntro. wp_pures. wp_lam. wp_pures.
      by iApply ("IH" with "AU").
Qed.

End proof.
