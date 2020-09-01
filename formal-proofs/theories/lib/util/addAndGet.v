From iris.heap_lang Require Import notation lang.

Definition addAndGet: val :=
  rec: "addAndGet" "loc" "delta" :=
    let: "cur" := !"loc" in
    let: "new" := "cur" + "delta" in
    if: CAS "loc" "cur" "new"
    then "new"
    else "addAndGet" "loc" "delta".

From iris.program_logic Require Import atomic.
From iris.heap_lang Require Import proofmode.

Section proof.

Context `{heapG}.

Theorem addAndGet_spec (ℓ: loc) (Δ: Z):
  ⊢ <<< ∀ (k: Z), ▷ ℓ ↦ #k >>>
    addAndGet #ℓ #Δ @ ⊤
  <<< ℓ ↦ #(k + Δ), RET #(k + Δ) >>>.
Proof.
  iIntros (Φ) "AU". iLöb as "IH". wp_lam. wp_pures.
  wp_bind (!_)%E. iMod "AU" as (k) "[Hℓ [HClose _]]".
  wp_load. iMod ("HClose" with "Hℓ") as "AU". iModIntro. wp_pures.
  wp_bind (CmpXchg _ _ _). iMod "AU" as (k') "[Hℓ HClose]".
  destruct (decide (k = k')) as [<-|HContra].
  - wp_cmpxchg_suc. iDestruct "HClose" as "[_ HClose]".
    iMod ("HClose" with "Hℓ") as "HΦ".
    iModIntro. wp_pures. iAssumption.
  - wp_cmpxchg_fail. iDestruct "HClose" as "[HClose _]".
    iMod ("HClose" with "Hℓ") as "AU".
    iModIntro. wp_pures. iApply ("IH" with "AU").
Qed.

End proof.
