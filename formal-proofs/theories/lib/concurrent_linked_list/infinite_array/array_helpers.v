From iris.program_logic Require Import atomic.
From iris.heap_lang Require Export proofmode notation lang.
Require Export SegmentQueue.lib.concurrent_linked_list.infinite_array.array_spec.

Section impl.

Variable (array_interface: infiniteArrayInterface).

Definition findCellAndMoveForward: val :=
  λ: "ptr" "id" "startFrom",
  (rec: "loop" <> := let: "cell" := findCell array_interface "startFrom" "id" in
                    if: cutoffMoveForward array_interface "ptr" "cell"
                    then "cell"
                    else "loop" #()) #().

End impl.

Section proof.

Context `{!heapG Σ}.

Variable (array_interface: infiniteArrayInterface).
Variable (aspc: infiniteArraySpec Σ array_interface).

Theorem findCellAndMoveForward_spec N γ co p (v: val) (source_id id: nat):
  is_infinite_array _ _ aspc N γ co -∗
  is_infinite_array_cutoff_reading _ _ aspc N γ p source_id -∗
  <<< ∀ start_index, ▷ is_infinite_array_cutoff _ _ aspc N γ v start_index >>>
      findCellAndMoveForward array_interface v #id p @ ⊤ ∖ ↑N
  <<< ∃ p' id', is_infinite_array_cell_pointer _ _ aspc N γ p' id'
                ∗ ⌜(id ≤ id')%nat⌝
                ∗ (∀ i, (⌜max source_id id ≤ i < id'⌝)%nat
                        -∗ cell_is_cancelled _ _ aspc N γ i
                        ∗ (∃ ℓ, infinite_array_mapsto _ _ aspc N co γ i ℓ))
                ∗ ∃ i', ⌜start_index ≤ i' ≤ max id' start_index⌝ ∧
                  is_infinite_array_cutoff _ _ aspc N γ v i',
  RET p' >>>.
Proof.
  iIntros "#HArr #HReading" (Φ) "AU". wp_lam. wp_pures. iLöb as "IH".
  wp_bind (findCell _ _ _). iApply (findCell_spec with "[$]").
  iIntros (p' id') "!> (#HCellPointer & % & #HCancelled)". wp_pures.
  wp_bind (cutoffMoveForward _ _ _).
  awp_apply (cutoffMoveForward_spec with "HArr HCellPointer").
  iApply (aacc_aupd with "AU"); first done.
  iIntros (start_index) "HCutoff". iAaccIntro with "HCutoff".
  by iIntros "$ !> $ !> //".
  iIntros ([|]) "HResult".
  - iRight. iExists p', id'.
    iSplitL; last by iIntros "!> HΦ !>"; wp_pures.
    by iFrame "HCellPointer HCancelled HResult".
  - iLeft. iFrame "HResult". iIntros "!> AU !>". wp_pures.
    by iApply ("IH" with "AU").
Qed.

End proof.
