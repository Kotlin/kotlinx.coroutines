From iris.heap_lang Require Import notation lang.

Definition addConditionally: val :=
  rec: "addConditionally" "loc" "delta" "condition" :=
    let: "cur" := !"loc" in
    if: "condition" "cur"
    then if: CAS "loc" "cur" ("cur" + "delta")
         then #true
         else "addConditionally" "loc" "delta" "condition"
    else #false.

From iris.program_logic Require Import atomic.
From iris.heap_lang Require Import proofmode.

Section proof.

Context `{heapG}.

Theorem addConditionally_spec (pred: Z → bool) (ℓ: loc) (Δ: Z) (condition: val):
  ⊢ (∀ (k: Z), {{{ True }}}
                 condition #k
               {{{ RET #(pred k); True }}}) →
    <<< ∀ (k: Z), ▷ ℓ ↦ #k >>>
      addConditionally #ℓ #Δ condition @ ⊤
    <<< if pred k then ℓ ↦ #(k + Δ) else ℓ ↦ #k, RET #(pred k) >>>.
Proof.
  iIntros "#HCond" (Φ) "AU". iLöb as "IH". wp_lam. wp_pures.
  wp_bind (!_)%E. iMod "AU" as (k) "[Hℓ HClose]".
  wp_load.
  destruct (pred k) eqn:E; wp_pures.
  - iDestruct "HClose" as "[HClose _]".
    iMod ("HClose" with "Hℓ") as "AU". iModIntro. wp_pures.
    wp_apply ("HCond" with "[$]"). iIntros (_).
    rewrite E. wp_pures.
    wp_bind (CmpXchg _ _ _). iMod "AU" as (k') "[Hℓ HClose]".
    destruct (decide (k = k')) as [<-|HContra].
    + wp_cmpxchg_suc. iDestruct "HClose" as "[_ HClose]".
      iMod ("HClose" with "[Hℓ]") as "HΦ".
      { rewrite E. iFrame. }
      iModIntro. wp_pures. rewrite E. iAssumption.
    + wp_cmpxchg_fail. iDestruct "HClose" as "[HClose _]".
      iMod ("HClose" with "Hℓ") as "AU".
      iModIntro. wp_pures. iApply ("IH" with "AU").
  - iDestruct "HClose" as "[_ HClose]".
    iMod ("HClose" with "[Hℓ]") as "AU"; first by iFrame.
    iModIntro. wp_pures.
    wp_apply ("HCond" with "[$]"). iIntros (_).
    rewrite E. wp_pures.
    iAssumption.
Qed.

End proof.
