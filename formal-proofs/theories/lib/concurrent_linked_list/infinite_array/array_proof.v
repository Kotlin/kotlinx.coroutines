From iris.program_logic Require Import atomic.
From iris.heap_lang Require Export proofmode notation lang.
From iris.algebra Require Import auth agree list.
From SegmentQueue.lib.concurrent_linked_list Require Import list_spec.
From SegmentQueue.lib.concurrent_linked_list.infinite_array Require Import
     sqsegment_proof array_impl array_spec.
Require Import SegmentQueue.util.everything.

Section array_impl.

Context `{heapG Σ} `{iSegmentG Σ}.

Variable (segment_size pointer_shift: positive).
Variable (limit: Pos.to_nat segment_size < 2 ^ Pos.to_nat pointer_shift).
Variable list_impl: listInterface.
Let node_spec' := node_segment segment_size pointer_shift limit.
Variable list_spec': ∀ N, listSpec Σ list_impl (node_spec' N _ _ _).
Variable (N: namespace).
Let NList := N .@ "list".
Let NNode := N .@ "node".
Let list_spec := list_spec' NNode.
Let node_spec := node_spec' NNode _ _ _.
Let array_impl := InfiniteArray segment_size pointer_shift list_impl.

Definition is_infinite_array γ
           (cell_is_owned: nat -> iProp Σ) :=
  is_concurrentLinkedList _ _ _ list_spec NList cell_is_owned γ.

Global Instance is_infinite_array_persistent γ cell_is_owned:
  Persistent (is_infinite_array γ cell_is_owned).
Proof. apply _. Qed.

Let segment_size_nat := Pos.to_nat segment_size.

Definition segment_view γ i f: iProp Σ :=
  ∃ γs v, segment_in_list _ _ _ list_spec γ γs (i `div` segment_size_nat) v ∗
          has_value id_uniqueValue γs (i `div` segment_size_nat) ∗
          f γs (i `mod` segment_size_nat) v.

Definition infinite_array_mapsto cell_is_owned γ i ℓ: iProp Σ :=
  segment_view γ i (fun γs ix v =>
  is_node segment_size NNode cell_is_owned γs v ∗
  ∃ dℓ, has_value dataLocation_uniqueValue γs dℓ ∗ ⌜ℓ = dℓ +ₗ ix⌝)%I.

Global Instance infinite_array_mapsto_persistent co γ i ℓ:
  Persistent (infinite_array_mapsto co γ i ℓ).
Proof. apply _. Qed.

Theorem infinite_array_mapsto_agree co γ i ℓ ℓ':
  infinite_array_mapsto co γ i ℓ -∗ infinite_array_mapsto co γ i ℓ' -∗ ⌜ℓ = ℓ'⌝.
Proof.
  iIntros "H1 H2". rewrite /infinite_array_mapsto.
  iDestruct "H1" as (? ?) "(H1 & _ & [_ H1Rest])".
  iDestruct "H2" as (? ?) "(H2 & _ & [_ H2Rest])".
  iDestruct (segment_in_list_agree with "H1 H2") as "[-> ->]".
  iDestruct "H1Rest" as (?) "[H1dℓ ->]".
  iDestruct "H2Rest" as (?) "[H2dℓ ->]".
  iDestruct (has_value_agrees with "H1dℓ H2dℓ") as %->.
  by iPureIntro.
Qed.

Definition is_infinite_array_cell_pointer γ (p: val) (i: nat): iProp Σ :=
  segment_view γ i (fun γs ix v => ⌜p = (v, #ix)%V⌝)%I.

Global Instance is_infinite_array_cell_pointer_persistent γ p i:
  Persistent (is_infinite_array_cell_pointer γ p i).
Proof. apply _. Qed.

Definition is_infinite_array_cutoff_reading γ (p: val) (i: nat): iProp Σ :=
  ∃ γs, segment_in_list _ _ _ list_spec γ γs (i `div` segment_size_nat) p ∗
        ⌜i `mod` segment_size_nat = 0⌝.

Global Instance is_infinite_array_cutoff_reading_persistent γ p i:
  Persistent (is_infinite_array_cutoff_reading γ p i).
Proof. apply _. Qed.

Definition is_infinite_array_cutoff γ (v: val) (i: nat): iProp Σ :=
  ∃ (ℓ: loc), ⌜v = #ℓ ∧ i `mod` segment_size_nat = 0⌝ ∧
              pointer_location _ _ _ list_spec γ ℓ (i `div` segment_size_nat).

Definition cell_is_cancelled' γ i: iProp Σ :=
  segment_view γ i (fun γs ix v => sqsegment_proof.cell_is_cancelled γs ix).

Global Instance cell_is_cancelled'_persistent γ i:
  Persistent (cell_is_cancelled' γ i).
Proof. apply _. Qed.

Definition cell_cancellation_handle' γ i: iProp Σ :=
  segment_view γ i (fun γs ix v => sqsegment_proof.cell_cancellation_handle γs ix).

Theorem cell_cancellation_handle'_exclusive γ i:
  cell_cancellation_handle' γ i -∗ cell_cancellation_handle' γ i -∗ False.
Proof.
  iIntros "H1 H2". rewrite /infinite_array_mapsto.
  iDestruct "H1" as (? ?) "(H1 & _ & H1Rest)".
  iDestruct "H2" as (? ?) "(H2 & _ & H2Rest)".
  iDestruct (segment_in_list_agree with "H1 H2") as "[-> ->]".
  iDestruct (sqsegment_proof.cell_cancellation_handle_exclusive
               with "H1Rest H2Rest") as %[].
Qed.

Theorem cell_cancellation_handle'_not_cancelled γ i:
  cell_is_cancelled' γ i -∗ cell_cancellation_handle' γ i -∗ False.
Proof.
  iIntros "H1 H2".
  iDestruct "H1" as (? ?) "(H1 & _ & H1Rest)".
  iDestruct "H2" as (? ?) "(H2 & _ & H2Rest)".
  iDestruct (segment_in_list_agree with "H1 H2") as "[-> ->]".
  iDestruct (cell_with_handle_not_cancelled with "H1Rest H2Rest") as %[].
Qed.

Theorem acquire_cell cell_is_owned E γ i ℓ:
    ↑N ⊆ E →
    infinite_array_mapsto cell_is_owned γ i ℓ ={E, E∖↑N}=∗
    ▷ (cell_is_owned i ∨ ℓ ↦ NONEV ∗ cell_cancellation_handle' γ i) ∗
    (▷ (cell_is_owned i ∨ ℓ ↦ NONEV ∗ cell_cancellation_handle' γ i)
    ={E∖↑N, E}=∗ True).
Proof.
  iIntros (HMask) "#HMapsto".
  iDestruct "HMapsto" as (? ?) "[HSeg (HId & HNode & Hdℓ)]".
  iDestruct "Hdℓ" as (dℓ) "[Hdℓ ->]".
  iDestruct "HNode" as (?) "[-> HRest]".
  iDestruct "HRest" as (values) "(#HInv & #HValues & #HHeap & Hℓ)".
  iDestruct "HId" as (v'') "[HValues'' %]".
  iDestruct "Hdℓ" as (v') "[HValues' <-]".
  iDestruct (own_valid_2 with "HValues HValues'") as %[_ HValid]%pair_valid.
  iDestruct (own_valid_2 with "HValues HValues''") as %[_ HValid']%pair_valid.
  move: HValid HValid'=> /=. rewrite -!Some_op !Some_valid=> HAgree HAgree'.
  apply agree_op_invL' in HAgree. apply agree_op_invL' in HAgree'. subst v' v''.
  rewrite /NNode.
  iInv "HInv" as "HOpen" "HClose".
  iAssert (|={E ∖ ↑N.@"node", E ∖ ↑N}=> |={E ∖ ↑N, E ∖ ↑N.@"node"}=> emp)%I
    as ">HMod".
  { iApply (fupd_intro_mask'). apply difference_mono_l, nclose_subseteq. }
  iDestruct (big_sepL_lookup_acc _ _ (i `mod` Pos.to_nat segment_size)
               with "HOpen") as "[HElement HRestore]".
  { rewrite lookup_seq /=. split; first done.
    apply Nat.mod_upper_bound. lia. }
  rewrite /segment_invariant.
  replace (segmentId values) with (i `div` Pos.to_nat segment_size) by auto.
  replace ((_ `div` _) * _ + (_ `mod` _)) with i;
    last by rewrite Nat.mul_comm -Nat.div_mod; lia.
  iModIntro. iSplitL "HElement".
  {
    iDestruct "HElement" as "[HElement|HElement]"; first by iLeft.
    iRight. iDestruct "HElement" as "[$ HCanc]".
    rewrite /cell_cancellation_handle' /= /segment_view /=.
    iExists _, _. iFrame "HSeg HCanc".
    iExists values. iFrame "HValues". by iPureIntro.
  }
  iIntros "HOwned". iMod "HMod" as "_".
  iMod ("HClose" with "[-]"); last done.
  iApply "HRestore".
  iDestruct "HOwned" as "[$|[Hℓ' HHandle]]". iRight. iFrame.
  iDestruct "HHandle" as (? ?) "(HSeg' & ? & ?)".
  iDestruct (segment_in_list_agree with "HSeg HSeg'") as ">[% %]".
  simplify_eq. iFrame.
Qed.

Theorem cancelCell_spec γ co p i:
  is_infinite_array γ co -∗
  is_infinite_array_cell_pointer γ p i -∗
  <<< ▷ cell_cancellation_handle' γ i >>>
  cancelCell array_impl p @ ⊤ ∖ ↑N
  <<< ▷ cell_is_cancelled' γ i, RET #() >>>.
Proof.
  iIntros "#HArr #HCellPointer" (Φ) "AU". wp_lam.
  rewrite /is_infinite_array_cell_pointer.
  iDestruct "HCellPointer" as (? ?) "(#HInList & #HId & ->)".
  wp_pures.
  awp_apply (onSlotCleaned_spec with "HArr HInList").
  {
    iIntros "HCancHandle !>" (n) "HSegContent".
    iMod (cancel_cell with "HCancHandle HSegContent") as
        "[#HCellCancelled HSegContent']"; try done.
    iSplitR. by iApply "HCellCancelled".
    iDestruct "HSegContent'" as (? ->) "HSegContent". iExists _.
    iSplitR; first by iPureIntro. done.
  }
  iApply (aacc_aupd_commit with "AU").
  by apply difference_mono_l, nclose_subseteq.
  iIntros "HCancHandle".
  iDestruct "HCancHandle" as (? ?) "(#HInList' & #HId' & >HCancHandle)".
  iDestruct (segment_in_list_agree with "HInList HInList'") as ">[-> ->]".
  iAaccIntro with "HCancHandle".
  {
    iIntros "HCancHandle !>". iSplitL; last by iIntros "$ //".
    iExists _, _. by iFrame "HInList HId'".
  }
  iIntros "#HCellCancelled !>". iSplit.
  - iExists _, _. by iFrame "HInList HId' HCellCancelled".
  - iIntros "$ !> //".
Qed.

Lemma logicallyDerefCellPointer E P co γ i:
  ↑NList ⊆ E ->
  is_infinite_array γ co -∗
  segment_view γ i P ={E}=∗
  ∃ ℓ, ▷ infinite_array_mapsto co γ i ℓ.
Proof.
  iIntros (HMask) "#HArr HCellPointer".
  iDestruct "HCellPointer" as (? ?) "(#HInList & #HId & _)".
  iMod (segment_in_list_is_node with "HArr HInList") as "#[HNode HId']";
    first done.
  iDestruct "HId" as (values) "[HOwn HId]".
  iExists _, _, _. iFrame "HInList HNode HId'". simpl.
  iExists _. iSplitL; last done. iExists _. by iFrame "HOwn".
Qed.

Theorem findCell_spec γ co p (source_id id: nat):
  {{{ is_infinite_array γ co ∗
      is_infinite_array_cutoff_reading γ p source_id }}}
  findCell array_impl p #id @ ⊤
  {{{ p' id', RET p'; is_infinite_array_cell_pointer γ p' id'
      ∗ ⌜(id ≤ id')%nat⌝
      ∗ ∀ i, (⌜max source_id id ≤ i < id'⌝)%nat -∗
             cell_is_cancelled' γ i ∗ ∃ ℓ, infinite_array_mapsto co γ i ℓ
  }}}.
Proof.
  iIntros (Φ) "[#HArr #HCellPointer] HΦ".
  iDestruct "HCellPointer" as (?) "[#HInList _]".

  wp_lam. wp_pures. wp_bind (findSegment _ _ _).
  rewrite quot_of_nat /is_infinite_array.
  iApply (findSegment_spec with "[]"); first by iFrame "HInList HArr".
  iIntros (v' id') "!> HResult".
  iDestruct "HResult" as "(HInList' & HFound & #HCancelled)".
  iDestruct "HFound" as %HFound. iDestruct "HInList'" as (γs') "#HInList'".
  iMod (segment_in_list_is_node with "HArr HInList'") as "#[HNode' HId']";
    first done.
  wp_lam. wp_pures. wp_bind (getIdImpl _ _ _).
  iApply (getId_spec segment_size pointer_shift with "HNode'").
  iIntros (id'') "!> HId''".
  iDestruct (has_value_agrees with "HId' HId''") as "<-".

  iApply fupd_wp.
  iMod (segment_implies_preceding_segments with "HArr HInList'")
    as "#HOthersInList"; first done.
  iAssert (∀ i, ⌜source_id `max` id ≤ i ∧ i < id' * segment_size_nat⌝ ={⊤}=∗
           cell_is_cancelled' γ i)%I with "[]" as "#HCellCanc".
  {
    iIntros (i HBound).
    assert ((source_id `div` segment_size_nat) `max`
            (id `div` Pos.to_nat segment_size) ≤
            i `div` segment_size_nat ∧ i `div` segment_size_nat < id').
    {
      move: HBound. clear.
      split.
      - destruct (decide (source_id ≤ id)) as [HLe|HGt].
        * rewrite Nat.max_r; last (apply Nat.div_le_mono; lia).
          apply Nat.div_le_mono; lia.
        * rewrite Nat.max_l; last (apply Nat.div_le_mono; lia).
          apply Nat.div_le_mono; lia.
      - rewrite (Nat.mul_lt_mono_pos_r segment_size_nat); last lia.
        assert (segment_size_nat * i `div` segment_size_nat ≤ i); last lia.
        apply Nat.mul_div_le; lia.
    }
    iAssert (∃ γs v, segment_in_list _ _ _ _ γ γs (i `div` segment_size_nat) v)%I
            with "[]" as (γsc vc) "#HCInList".
    { iApply "HOthersInList". iPureIntro. lia. }
    iMod (segment_in_list_is_node with "HArr HCInList") as "[_ #>HCId]";
      first done.
    iMod (access_segment _ _ _ _ _ _ true with "HArr HCInList []") as (n) "HEl";
      first done.
    { iApply "HCancelled". iPureIntro. lia. }
    iDestruct "HEl" as "([%| ->] & >HContent & HClose)"; first done.
    rewrite /= /segment_spec.segment_content /segment_content /=.
    iDestruct "HContent" as (values state [HMatching HLength]) "H●".
    iExists _, _. iFrame "HCInList HCId".
    iMod (own_update with "H●") as "[H● $]".
    2: iMod ("HClose" with "[H●]") as "_"; last done;
      first by iExists _, _; iFrame "H●".
    rewrite /algebra_from_list.
    apply prod_update; simpl; last by rewrite ucmra_unit_right_id.
    apply auth_update_core_id; first by apply _.
    apply list_singletonM_included.
    assert (is_Some (state !! (i `mod` segment_size_nat))) as [cst HLookup].
    { apply lookup_lt_is_Some. rewrite HLength /segment_size_nat.
      apply Nat.mod_upper_bound. lia. }
    eexists. rewrite map_lookup HLookup /=. split; first done.
    apply Some_included. left.
    destruct cst=> /=; last done.
    exfalso.
    move: HMatching HLookup. remember (_ `mod` _) as k. clear.
    move: k.
    induction state as [|x state']; first done.
    simpl. destruct (decide (x = cellAlive)); first done.
    destruct k=> /=; last by eauto.
    intros; simplify_eq.
  }
  iAssert (∀ i, ⌜source_id `max` id ≤ i ∧ i < id' * segment_size_nat⌝ ={⊤}=∗
          ∃ ℓ, ▷ infinite_array_mapsto co γ i ℓ)%I with "[]" as "#HMapsto".
  { iIntros (i HEl).
    iAssert (|={⊤}=> cell_is_cancelled' γ i)%I with "[]" as ">HiCancelled";
      first by iApply "HCellCanc".
    by iMod (logicallyDerefCellPointer with "HArr HiCancelled") as "HH".
  }
  iAssert ([∗ list] i ∈ seq (source_id `max` id)
                    (id' * segment_size_nat - (source_id `max` id)),
          □ |={⊤}=> ▷ (cell_is_cancelled' γ i ∗
                      ∃ ℓ, infinite_array_mapsto co γ i ℓ))%I
    with "[]" as "HCellCanc'".
  {
    rewrite big_sepL_forall. iIntros (k ? HLookup).
    apply lookup_seq in HLookup.
    iModIntro. iSplitR.
    by iMod ("HCellCanc" $! _ with "[%]") as "$"; [lia|done].
    iMod ("HMapsto" $! _ with "[%]") as (ℓ) "HMapsto'"; last by iExists ℓ.
    lia.
  }
  iAssert (|={⊤}=> ▷ [∗ list] i ∈ seq (source_id `max` id)
                    (id' * segment_size_nat - (source_id `max` id)),
          cell_is_cancelled' γ i ∗
          ∃ ℓ, infinite_array_mapsto co γ i ℓ)%I with "[]" as ">#HCellCanc''".
  {
    iEval (rewrite big_sepL_later). iApply big_sepL_fupd.
    iApply (big_sepL_mono with "HCellCanc'").
    iIntros (k y HSeq) "#HPers"=> //=.
  }
  iClear "HCellCanc HCellCanc' HOthersInList".
  iAssert (▷ ∀ i, ⌜source_id `max` id ≤ i ∧ i < id' * segment_size_nat⌝ -∗
           cell_is_cancelled' γ i ∗ ∃ ℓ, infinite_array_mapsto co γ i ℓ)%I
    with "[]" as "#HCellCanc".
  {
    iIntros (k [Hk1 Hk2]). rewrite big_sepL_forall.
    apply nat_le_sum in Hk1. destruct Hk1 as [z ->].
    iApply "HCellCanc''". iPureIntro. apply (lookup_seq _ _ z). lia.
  }
  iClear "HCellCanc''".
  iModIntro. rewrite rem_of_nat'; last lia.

  iMod (segment_in_list_is_node with "HArr HInList") as "#[HNode HId]";
    first done.

  wp_pures.

  rewrite bool_decide_decide. destruct (decide _) as [HEq|HNeq]; wp_pures.
  - simplify_eq.
    iApply "HΦ"; repeat iSplit.
    + iExists _, _. by iFrame "HInList' HId'".
    + by iPureIntro; lia.
    + iIntros (i HBound). iApply "HCellCanc". iPureIntro. lia.
  - iApply ("HΦ" $! _ (id' * segment_size_nat)).
    assert (id ≤ id' * segment_size_nat) as HLt'.
    {
      assert (id `div` segment_size_nat < id') as HLt.
      {
        destruct (decide (id' = id `div` segment_size_nat)) as [HContra|HH].
        - rewrite -HContra in HNeq. exfalso. apply HNeq. done.
        - unfold segment_size_nat in *. lia.
      }
      move: HLt. clear=> HLt. apply nat_lt_sum in HLt.
      destruct HLt as [z ->]. rewrite Nat.mul_add_distr_r /=.
      rewrite [in id in id ≤ _](Nat.div_mod id segment_size_nat); last lia.
      assert (id `mod` segment_size_nat < segment_size_nat).
      by apply Nat.mod_upper_bound; lia.
      lia.
    }
    repeat iSplit.
    + iExists _, _. rewrite Nat.div_mul; last lia. iFrame "HInList' HId'".
      iPureIntro. rewrite Nat.mod_mul; last lia. done.
    + iPureIntro. lia.
    + iIntros (i HBound). iApply "HCellCanc". iPureIntro. lia.
Qed.

Theorem derefCellPointer_spec co γ (p: val) i:
  {{{ is_infinite_array γ co ∗ is_infinite_array_cell_pointer γ p i }}}
    derefCellPointer array_impl p
  {{{ ℓ, RET #ℓ; infinite_array_mapsto co γ i ℓ }}}.
Proof.
  iIntros (Φ) "[#HArr #HCellPointer] HΦ". wp_lam.
  iDestruct "HCellPointer" as (? ?) "(#HInList & #HId & ->)".
  iMod (segment_in_list_is_node with "HArr HInList") as "#[HNode _]";
    first done.
  wp_pures. wp_lam.
  iDestruct "HNode" as (ℓ -> values) "#(HInv & HValues & #HHeapInv & HLoc)".
  wp_bind (! _)%E.
  iMod (inv_mapsto_acc with "HHeapInv HLoc") as (?) "(-> & Hℓ & HℓRestore)";
    first done.
  wp_load. iMod ("HℓRestore" with "Hℓ") as "_". iModIntro. wp_pures.
  iApply "HΦ". iExists _, _. iFrame "HInList HId".
  iSplit.
  - iExists _; iSplit; first done.
    iExists _; iFrame "HInv HValues HHeapInv HLoc".
  - iExists _; iSplit; last done.
    iExists _. by iFrame "HValues".
Qed.

Theorem cutoffMoveForward_spec co γ (p v: val) i:
  is_infinite_array γ co -∗
  is_infinite_array_cell_pointer γ p i -∗
  <<< ∀ start_index, ▷ is_infinite_array_cutoff γ v start_index >>>
    cutoffMoveForward array_impl v p @ ⊤ ∖ ↑N
  <<< ∃ (success: bool), if success
      then ∃ i', ⌜start_index ≤ i' ≤ max i start_index⌝ ∧
                 is_infinite_array_cutoff γ v i'
      else ▷ is_infinite_array_cutoff γ v start_index, RET #success >>>.
Proof.
  iIntros "#HArr #HCellPointer" (Φ) "AU".
  iDestruct "HCellPointer" as (? ?) "(#HInList & #HId & ->)".
  iApply fupd_wp. iMod "AU" as (?) "[HOpen [HClose _]]".
  iDestruct "HOpen" as (ℓ) "[>[-> %] HView]".
  iMod ("HClose" with "[HView]") as "AU"; first by iExists ℓ; by iSplitR.
  iModIntro. wp_lam. wp_pures.
  awp_apply (moveForward_spec with "HArr HInList").
  iApply (aacc_aupd_commit with "AU").
  { apply difference_mono_l, nclose_subseteq. }
  iIntros (start_index) "HCutoff".
  iDestruct "HCutoff" as (ℓ') "[>Hℓ' HView]".
  iDestruct "Hℓ'" as %[Hℓ' HMod]; simplify_eq.
  iAaccIntro with "HView".
  {
    iIntros "HPtr !>". iSplitL; last by iIntros "$ !> //".
    iExists _. iSplitR; first done. iFrame.
  }
  iIntros (result) "HResult". iExists result.
  iSplitL; last by iIntros "!> $ !> //".
  destruct result.
  - destruct (decide (i ≤ start_index)) as [HLe|HGt].
    * rewrite !Nat.max_r.
      2: lia.
      2: apply Nat.div_le_mono; lia.
      iExists start_index. iSplitR; first done.
      iExists _. iFrame; done.
    * rewrite !Nat.max_l.
      2: lia.
      2: apply Nat.div_le_mono; lia.
      iExists (segment_size_nat * (i `div` segment_size_nat)).
      iSplitR.
      + iPureIntro. split.
        2: by rewrite [in i in _ ≤ i] (Nat.div_mod i segment_size_nat); lia.
        rewrite [in start_index] (Nat.div_mod start_index segment_size_nat);
          last lia.
        rewrite HMod Nat.add_0_r.
        apply mult_le_compat_l, Nat.div_le_mono; lia.
      + iExists _.
        rewrite Nat.mul_comm Nat.mod_mul; last lia.
        rewrite Nat.div_mul; last lia.
        by iFrame "HResult".
  - iDestruct "HResult" as "[HPointerLoc #HSegmentCanc]".
    by iExists _; iSplitR.
Qed.

Theorem cutoffGetPointer_spec γ (v: val):
  ⊢ <<< ∀ i, ▷ is_infinite_array_cutoff γ v i >>>
    cutoffGetPointer array_impl v @ ⊤
  <<< ∃ (p: val), is_infinite_array_cutoff γ v i ∗
      is_infinite_array_cutoff_reading γ p i, RET p >>>.
Proof.
  iIntros (Φ) "AU". iApply fupd_wp.
  iMod "AU" as (?) "[HOpen [HClose _]]".
  iDestruct "HOpen" as (ℓ') "[>[-> HMod] HOpen]".
  iDestruct "HMod" as %HMod1.
  iMod ("HClose" with "[HOpen]") as "AU"; first by iExists _; iSplitR.
  iModIntro. wp_lam.
  awp_apply pointer_location_load.
  iApply (aacc_aupd_commit with "AU"); first done.
  iIntros (start_index) "HCutoff".
  iDestruct "HCutoff" as (ℓ) "[>[% %] HOpen]"; simplify_eq.
  iAaccIntro with "HOpen".
  {
    iIntros "H !>". iSplitL; last by iIntros "$ !> //".
    iExists _. by iSplitR.
  }
  iIntros (? ?) "[HPointerLoc #HInList]".
  iExists _. iSplitL; last by iIntros "!> HΦ !>"; wp_pures.
  iSplitL.
  by iExists _; iSplitR.
  iExists _. by iFrame "HInList".
Qed.

Theorem cellPointerId_spec co γ (p: val) i:
  {{{ is_infinite_array γ co ∗ is_infinite_array_cell_pointer γ p i }}}
    cellPointerId array_impl p
  {{{ RET #i; True }}}.
Proof.
  iIntros (Φ) "[#HArr #HCellPointer] HΦ". wp_lam.
  iDestruct "HCellPointer" as (? ?) "(#HInList & #HId & ->)".
  iMod (segment_in_list_is_node with "HArr HInList") as "#[HNode _]";
    first done.
  wp_pures.
  wp_apply (getId_spec segment_size pointer_shift with "HNode").
  iIntros (id) "HId'".
  iDestruct (has_value_agrees with "HId HId'") as %<-. wp_pures.
  rewrite -Nat2Z.inj_mul -Nat2Z.inj_add /segment_size_nat Nat.mul_comm.
  rewrite -Nat.div_mod; last lia. iApply "HΦ"; last done.
Qed.

Theorem cellPointerCleanPrev_spec co γ (p: val) i:
  {{{ is_infinite_array γ co ∗ is_infinite_array_cell_pointer γ p i }}}
    cellPointerCleanPrev array_impl p
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "[#HArr #HCellPointer] HΦ". wp_lam.
  iDestruct "HCellPointer" as (? ?) "(#HInList & #HId & ->)".
  iMod (segment_in_list_is_node with "HArr HInList") as "#[HNode _]";
    first done.
  wp_pures.
  iApply cleanPrev_spec; last by iApply "HΦ". iFrame "HInList HArr".
Qed.

Theorem newInfiniteArray_spec co k:
  {{{ ⌜(k > 0)%nat⌝ ∧ inv_heap_inv }}}
    newInfiniteArray array_impl #k
  {{{ γ ℓ, RET #ℓ; is_infinite_array γ co ∗
                   [∗ list] i ∈ seq 0 k,
                     is_infinite_array_cutoff γ #(ℓ +ₗ Z.of_nat i) 0
  }}}.
Proof.
  iIntros (Φ) "HInit HΦ". rewrite /newInfiniteArray.
  iApply (newList_spec _ _ node_spec with "HInit").
  iIntros (γ ℓ) "!> [HList HPtrs]". iApply "HΦ".
  iFrame "HList". iApply (big_sepL_mono with "HPtrs").
  iIntros (? ? HLookup) "HPtrLoc".
  iExists _.
  rewrite Nat.div_0_l; last lia. rewrite Nat.mod_0_l; last lia.
  iFrame "HPtrLoc". done.
Qed.

End array_impl.

Canonical Structure array_impl
          (segment_size pointer_shift: positive)
          (limit: Pos.to_nat segment_size < 2 ^ Pos.to_nat pointer_shift)
          {list_impl: listInterface}
          `{!heapG Σ} `{iSegmentG Σ}
          (list_spec: ∀ (N: namespace), listSpec Σ list_impl (node_segment segment_size pointer_shift limit N))
          {impl: segmentInterface} (segment_spec: segmentSpec Σ impl)
          `{!iLinkedListG segment_spec Σ} :=
  {|
  array_spec.newInfiniteArray_spec := newInfiniteArray_spec segment_size pointer_shift limit list_impl list_spec;
  array_spec.findCell_spec := findCell_spec segment_size pointer_shift limit list_impl list_spec;
  array_spec.cancelCell_spec := cancelCell_spec segment_size pointer_shift limit list_impl list_spec;
  array_spec.derefCellPointer_spec := derefCellPointer_spec segment_size pointer_shift limit list_impl list_spec;
  array_spec.cutoffMoveForward_spec := cutoffMoveForward_spec segment_size pointer_shift limit list_impl list_spec;
  array_spec.cutoffGetPointer_spec := cutoffGetPointer_spec segment_size pointer_shift limit list_impl list_spec;
  array_spec.infinite_array_mapsto_agree := infinite_array_mapsto_agree segment_size pointer_shift limit list_impl list_spec;
  array_spec.cell_cancellation_handle_exclusive := cell_cancellation_handle'_exclusive segment_size pointer_shift limit list_impl list_spec;
  array_spec.cell_cancellation_handle_not_cancelled := cell_cancellation_handle'_not_cancelled segment_size pointer_shift limit list_impl list_spec;
  array_spec.acquire_cell := acquire_cell segment_size pointer_shift limit list_impl list_spec;
  array_spec.cellPointerId_spec := cellPointerId_spec segment_size pointer_shift limit list_impl list_spec;
  array_spec.cellPointerCleanPrev_spec := cellPointerCleanPrev_spec segment_size pointer_shift limit list_impl list_spec;
  |}.
