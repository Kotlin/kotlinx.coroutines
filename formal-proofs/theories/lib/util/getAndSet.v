From iris.proofmode Require Import tactics.
From iris.program_logic Require Export atomic.
From iris.heap_lang Require Import proofmode notation lang.

Definition getAndSet : val :=
  rec: "getAndSet" "l" "v" :=
    let: "o" := ! "l" in
    if: CAS "l" "o" "v"
    then "o"
    else "getAndSet" "l" "v".

Section getAndSetProof.

Context `{heapG}.

Theorem getAndSet_spec (ℓ: loc) (v: val):
  ⊢ <<< ∀ k, ▷ ℓ ↦ k ∧ ⌜val_is_unboxed k⌝>>>
    getAndSet #ℓ v @ ⊤
  <<< ℓ ↦ v, RET k >>>.
Proof.
  iIntros (Φ) "AU". iLöb as "IH". wp_lam. wp_pures.
  wp_bind (!_)%E. iMod "AU" as (k) "[[Hℓ %] [HClose _]]".
  wp_load. iMod ("HClose" with "[Hℓ]") as "AU"; first by iSplit. iModIntro.
  wp_let. wp_bind (CmpXchg _ _ _)%E. iMod "AU" as (k') "[[Hℓ %] HClose]".
  destruct (decide (k = k')) as [[= ->]|Hx];
    [wp_cmpxchg_suc|wp_cmpxchg_fail];
    [iDestruct "HClose" as "[_ HClose]" | iDestruct "HClose" as "[HClose _]"].
  all: iMod ("HClose" with "[Hℓ]") as "HΦ"; first by auto.
  all: iModIntro; wp_pures; auto.
  by wp_apply "IH".
Qed.

End getAndSetProof.
