From iris.heap_lang Require Import notation.

Require Import SegmentQueue.lib.infinite_array.infinite_array_impl.
Require Import SegmentQueue.lib.infinite_array.iterator.
Require Import SegmentQueue.lib.util.getAndSet.
Require Import SegmentQueue.lib.util.interruptibly.

Section impl.

Variable segment_size: positive.

Notation RESUMEDV := (SOMEV #0).
Notation CANCELLEDV := (SOMEV #1).

Definition cancel_cell: val :=
  λ: "cell'",
  let: "cell" := cell_ref_loc "cell'" in
  if: getAndSet "cell" CANCELLEDV = RESUMEDV
  then segment_cancel_cell (Fst "cell")
  else #().

Definition move_ptr_forward : val :=
  rec: "loop" "ptr" "seg" := let: "curSeg" := !"ptr" in
                             if: segment_id "seg" ≤ segment_id "curSeg"
                             then #() else
                               if: CAS "ptr" "curSeg" "seg"
                               then #() else "loop" "ptr" "seg".

Definition park: val :=
  λ: "cancellationHandler" "cancHandle" "threadHandle",
  let: "r" := (loop: (λ: "c", ! "c")%V
               interrupted: "cancellationHandler") in
  "threadHandle" <- NONEV ;;
  "r".

Definition unpark: val :=
  λ: "threadHandle", "threadHandle" <- SOMEV #().

Definition suspend: val :=
  λ: "handler" "cancHandle" "threadHandle" "tail" "enqIdx",
  let: "cell'" := (iterator_step segment_size) "tail" "enqIdx" in
  move_ptr_forward "tail" (Fst "cell'") ;;
  let: "cell" := cell_ref_loc "cell'" in
  if: getAndSet "cell" (InjL "threadHandle") = RESUMEDV
  then #()
  else park ("handler" (cancel_cell "cell'")) "cancHandle" "threadHandle".

Definition resume: val :=
  rec: "resume" "head" "deqIdx" :=
    let: "cell'" := (iterator_step_skipping_cancelled segment_size)
                      "head" "deqIdx" in
    segment_cutoff (Fst "cell'") ;;
    move_ptr_forward "head" (Fst "cell'") ;;
    let: "cell" := cell_ref_loc "cell'" in
    let: "p" := getAndSet "cell" RESUMEDV in
    match: "p" with
        InjL "x" => if: "x" = #() then #() else unpark "x"
      | InjR "x" => "resume" "head" "deqIdx"
    end.

End impl.

From iris.heap_lang Require Import proofmode.

Section proof.

Context `{heapG Σ}.

Variable cell_is_processed: nat -> iProp Σ.

Variable ap: @infinite_array_parameters Σ.

Let segment_size := p_segment_size ap.

Context `{iArrayG Σ}.

Theorem move_ptr_forward_spec γ (v: loc) id ℓ:
  segment_location γ id ℓ -∗
  ([∗ list] j ∈ seq 0 (id * Pos.to_nat segment_size), cell_is_processed j) -∗
  <<< ∀ (id': nat) (ℓ': loc), ▷ is_infinite_array ap γ ∗ v ↦ #ℓ' ∗
                                         segment_location γ id' ℓ' >>>
    move_ptr_forward #v #ℓ @ ⊤
  <<< ▷ is_infinite_array ap γ ∗ (⌜id > id'⌝ ∗ v ↦ #ℓ ∨ ⌜id <= id'⌝ ∗ v ↦ #ℓ'),
  RET #() >>>.
Proof.
  iIntros "#HSegLoc HProc" (Φ) "AU". wp_lam. wp_pures. iLöb as "IH".
  wp_bind (!_)%E.
  iMod "AU" as (id' ℓ') "[[HIsInf [Htl #HLoc]] [HClose _]]".
  wp_load.
  iMod ("HClose" with "[HIsInf Htl HLoc]") as "AU"; first by iFrame.
  iModIntro. wp_pures.
  wp_bind (segment_id #ℓ').

  awp_apply segment_id_spec without "HProc".
  iApply (aacc_aupd_abort with "AU"); first done.
  iIntros (? ?) "[HIsInf HTl]".
  iDestruct (is_segment_by_location with "HLoc HIsInf")
    as (? ?) "[HIsSeg HArrRestore]".
  iAaccIntro with "HIsSeg"; iFrame; iIntros "HIsSeg"; iModIntro;
    iDestruct (bi.later_wand with "HArrRestore HIsSeg") as "$".
  by eauto.

  iIntros "AU !> HProc".

  awp_apply segment_id_spec without "HProc".
  iApply (aacc_aupd with "AU"); first done.
  iIntros (? ?) "[HIsInf HTl]".
  iDestruct (is_segment_by_location with "HSegLoc HIsInf")
    as (? ?) "[HIsSeg HArrRestore]".
  iAaccIntro with "HIsSeg"; iFrame; iIntros "HIsSeg"; iModIntro;
    iDestruct (bi.later_wand with "HArrRestore HIsSeg") as "$".
  by eauto.

  destruct (decide (id <= id')) eqn:E.
  {
    iRight. iSplitL.
    { iDestruct "HTl" as "[HTl HLoc']". iRight. iFrame. admit. }
    iIntros "HΦ !> HProc". wp_pures. rewrite bool_decide_decide E. by wp_pures.
  }
  iLeft. iFrame. iIntros "AU !> HProc". wp_pures. rewrite bool_decide_decide E.
  wp_pures.

  wp_bind (CmpXchg _ _ _).
  iMod "AU" as (id'' ℓ'') "[[HIsInf [Htl #HLocs]] HClose]".

  destruct (decide (ℓ'' = ℓ')); subst.
  {
    wp_cmpxchg_suc.
    iMod ("HClose" with "[HIsInf Htl]") as "HΦ".
    { iFrame. iLeft. iFrame. iPureIntro. admit. }
    iModIntro. by wp_pures.
  }
  {
    wp_cmpxchg_fail.
    iDestruct "HClose" as "[HClose _]".
    iMod ("HClose" with "[HIsInf Htl]") as "AU"; first by iFrame.
    iModIntro. wp_pures. wp_lam. wp_pures.
    iApply ("IH" with "HProc AU").
  }
Qed.
