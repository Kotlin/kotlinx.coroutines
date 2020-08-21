From iris.heap_lang Require Export proofmode notation lang.
Require Import SegmentQueue.lib.concurrent_linked_list.segment_interfaces.

Section SQSegment_impl.

Variable maxSlots: positive.
Variable pointerShift: positive.

Definition newSegment: val :=
  λ: "id" "prev" "pointers",
  ref ("id", ref ("pointers" ≪ #(Zpos pointerShift)), ref "prev", ref NONE,
       AllocN #(Zpos maxSlots) NONE).

Definition getPrevLoc: val :=
  λ: "this", Snd (Fst (Fst (!"this"))).

Definition getNextLoc: val :=
  λ: "this", Snd (Fst (!"this")).

Definition getCleanedAndPointersLoc: val :=
  λ: "this", Snd (Fst (Fst (Fst (!"this")))).

Definition getId: val :=
  λ: "this", Fst (Fst (Fst (Fst (!"this")))).

Definition getDataLoc: val :=
  λ: "this", Snd (!"this").

Definition SQSegmentListNode :=
  {| segment_interfaces.getPrevLoc := getPrevLoc;
     segment_interfaces.getNextLoc := getNextLoc;
  |}.

Definition SQSegment :=
  {| segment_interfaces.base := SQSegmentListNode;
     segment_interfaces.newSegment := newSegment;
     segment_interfaces.getId := getId;
     segment_interfaces.maxSlots := Pos.to_nat maxSlots;
     segment_interfaces.pointerShift := Pos.to_nat pointerShift;
     segment_interfaces.getCleanedAndPointersLoc := getCleanedAndPointersLoc
  |}.

End SQSegment_impl.

From iris.base_logic Require Import lib.invariants.
From iris.algebra Require Import cmra auth list agree csum excl gset frac.
Require Import SegmentQueue.lib.concurrent_linked_list.segment_spec.
Require Import SegmentQueue.util.everything.

Section infinite_array_segment_proof.

Context `{heapG Σ}.

Variable segment_size: positive.
Variable pointer_shift: positive.
Variable pointer_shift_bound:
  Pos.to_nat segment_size < 2 ^ Pos.to_nat pointer_shift.

Notation cell_algebra := (csumR (agreeR unitO) (* cell is cancelled *)
                                (exclR unitO)) (* cancellation permit exists *).

Record immutableValues :=
  ImmutableValues {
      segmentId: nat;
      segmentNextLocation: loc;
      segmentPrevLocation: loc;
      segmentCleanedAndPointersLocation: loc;
      segmentDataLocation: loc;
    }.

Inductive cellState := cellAlive
                     | cellCancelled.

Canonical Structure immutableValuesO := leibnizO immutableValues.

Notation segment_algebra :=
  (prodR
     (authUR (listUR (optionUR cell_algebra))) (* Cells *)
     (optionUR (agreeR immutableValuesO) (* Immutable contents of the segment *)
  )).

Class iSegmentG Σ := ISegmentG { iarray_inG :> inG Σ segment_algebra }.
Definition iSegmentΣ : gFunctors := #[GFunctor segment_algebra].
Instance subG_iSegmentΣ : subG iSegmentΣ Σ -> iSegmentG Σ.
Proof. solve_inG. Qed.
Context `{iSegmentG Σ}.

Notation iProp := (iProp Σ).

Let segment_size_nat := Pos.to_nat segment_size.

Definition cell_algebra_from_state (state: cellState): cell_algebra :=
  if state then Cinr (Excl ()) else Cinl (to_agree ()).

Definition algebra_from_list
           (values: immutableValues)
           (state: list cellState): segment_algebra :=
  (● ((fun (v: cellState) => Some (cell_algebra_from_state v)) <$> state),
   Some (to_agree values)).

Definition cell_is_cancelled γ id :=
  own γ (◯ {[ id := Some (cell_algebra_from_state cellCancelled) ]}, ε).

Global Instance cell_is_cancelled_persistent γ id:
  Persistent (cell_is_cancelled γ id).
Proof. apply _. Qed.

Definition cell_cancellation_handle γ id :=
  own γ (◯ {[ id := Some (cell_algebra_from_state cellAlive) ]}, ε).

Theorem cell_cancellation_handle_exclusive γ id:
  cell_cancellation_handle γ id -∗ cell_cancellation_handle γ id -∗ False.
Proof.
  iIntros "H1 H2".
  iDestruct (own_valid_2 with "H1 H2") as %HValid. exfalso. move: HValid.
  rewrite -pair_op. case=> /=.
  rewrite -auth_frag_op auth_frag_valid list_singletonM_op list_singletonM_valid//.
Qed.

Theorem cell_with_handle_not_cancelled γ id:
  cell_is_cancelled γ id -∗ cell_cancellation_handle γ id -∗ False.
  iIntros "H1 H2".
  iDestruct (own_valid_2 with "H1 H2") as %HValid. exfalso. move: HValid.
  rewrite -pair_op. case=> /=.
  rewrite -auth_frag_op auth_frag_valid list_singletonM_op list_singletonM_valid//.
Qed.

Lemma auth_cancel_cell values state γ id:
  cell_cancellation_handle γ id -∗
  own γ (algebra_from_list values state) ==∗
  own γ (algebra_from_list values (<[ id := cellCancelled ]> state)) ∗
  cell_is_cancelled γ id.
Proof.
  iIntros "HHandle Hγ".
  iMod (own_update_2 with "Hγ HHandle") as "[$ $]"; last done.
  apply prod_update; simpl; last done.
  apply auth_update, list_lookup_local_update=> i.
  rewrite list_fmap_insert.
  destruct (lt_eq_lt_dec i id) as [[HLt| ->]|HGt].
  - rewrite !list_lookup_singletonM_lt; try lia.
    rewrite list_lookup_insert_ne //; last lia.
  - rewrite !list_lookup_singletonM list_lookup_fmap.
    destruct (decide (id < length state)%nat) as [HLt|HGe].
    * rewrite list_lookup_insert; last by rewrite fmap_length.
      apply lookup_lt_is_Some in HLt.
      destruct HLt as [x ->]. simpl.
      apply option_local_update, option_local_update.
      rewrite /cell_algebra_from_state.
      destruct x.
      + apply replace_local_update; [apply _|done].
      + apply local_update_valid. intros _ _.
        case; first by intros HContra; inversion HContra.
        rewrite csum_included.
        case; first done.
        by case; intros (? & ? & ? & ? & ?).
    * apply local_update_valid.
      intros _ _.
      rewrite !lookup_ge_None_2; last lia.
      2: by rewrite insert_length fmap_length; lia.
      simpl.
      case; first by intros HContra; inversion HContra.
      intros HContra. by apply included_None in HContra.
  - rewrite !list_lookup_singletonM_gt; try lia.
    rewrite list_lookup_insert_ne //; last lia.
Qed.

Instance uniqueValue_fmap E: FMap (@uniqueValue Σ E).
Proof.
  intros A B f HUnique.
  eapply UniqueValue with
      (has_value := (fun γ v => ∃ v', has_value HUnique γ v' ∗ ⌜f v' = v⌝)%I);
    try apply _.
  iIntros (γ value1 value2) "H1 H2".
  iDestruct "H1" as (values1) "[H1 %]".
  iDestruct "H2" as (values2) "[H2 %]".
  iDestruct (has_value_agrees with "H1 H2") as "<-".
  by simplify_eq.
Defined.

Theorem immutableValues_uniqueValue: @uniqueValue Σ gname immutableValues.
Proof.
  eapply UniqueValue with
      (has_value := (fun γ values => own γ (ε, Some (to_agree values)))%I);
    try apply _.
  iIntros (γ v1 v2) "H1 H2".
  iDestruct (own_valid_2 with "H1 H2") as %[_ HValid]%pair_valid.
  iPureIntro. move: HValid; simpl. rewrite -Some_op Some_valid.
  intros HAgree. apply agree_op_invL' in HAgree. by inversion HAgree.
Defined.

Definition prev_uniqueValue :=
  segmentPrevLocation <$> immutableValues_uniqueValue.

Definition next_uniqueValue :=
  segmentNextLocation <$> immutableValues_uniqueValue.

Definition cleanedAndPointers_uniqueValue :=
  segmentCleanedAndPointersLocation <$> immutableValues_uniqueValue.

Definition id_uniqueValue :=
  segmentId <$> immutableValues_uniqueValue.

Definition dataLocation_uniqueValue :=
  segmentDataLocation <$> immutableValues_uniqueValue.

Variable (N: namespace).

Variable (cell_is_owned: nat -> iProp).

Definition segment_invariant (γ: gname) (values: immutableValues): iProp :=
  [∗ list] i ∈ seq 0 segment_size_nat,
  (cell_is_owned (segmentId values * segment_size_nat + i) ∨
   (segmentDataLocation values +ₗ i) ↦ NONEV ∗ cell_cancellation_handle γ i)%I.

Definition is_node γ (node: val): iProp :=
  ∃ (ℓ: loc), ⌜node = #ℓ⌝ ∧
              ∃ (values: immutableValues),
                inv N (segment_invariant γ values) ∗
                own γ (ε, Some (to_agree values)) ∗
                inv_heap_inv ∗
                ℓ ↦□ (fun v => v = (#(segmentId values),
                                    #(segmentCleanedAndPointersLocation values),
                                    #(segmentPrevLocation values),
                                    #(segmentNextLocation values),
                                    #(segmentDataLocation values))%V).

Global Instance is_node_persistent γ node: Persistent (is_node γ node).
Proof. apply _. Qed.

Theorem getPrevLoc_spec γ node:
  {{{ is_node γ node }}}
    getPrevLoc SQSegmentListNode node
  {{{ pℓ, RET #pℓ; has_value prev_uniqueValue γ pℓ }}}.
Proof.
  iIntros (Φ) "#HNode HΦ".
  iDestruct "HNode" as (ℓ -> values) "#(HInv & HValues & #HHeapInv & HLoc)".
  wp_lam. wp_bind (! _)%E.
  iMod (inv_mapsto_acc with "HHeapInv HLoc") as (?) "(-> & Hℓ & HℓRestore)";
    first done.
  wp_load. iMod ("HℓRestore" with "Hℓ") as "_". iModIntro. wp_pures.
  iApply "HΦ". iExists _. by iFrame "HValues".
Qed.

Theorem getNextLoc_spec γ node:
  {{{ is_node γ node }}}
    getNextLoc SQSegmentListNode node
  {{{ nℓ, RET #nℓ; has_value next_uniqueValue γ nℓ }}}.
Proof.
  iIntros (Φ) "#HNode HΦ".
  iDestruct "HNode" as (ℓ -> values) "#(HInv & HValues & #HHeapInv & HLoc)".
  wp_lam. wp_bind (! _)%E.
  iMod (inv_mapsto_acc with "HHeapInv HLoc") as (?) "(-> & Hℓ & HℓRestore)";
    first done.
  wp_load. iMod ("HℓRestore" with "Hℓ") as "_". iModIntro. wp_pures.
  iApply "HΦ". iExists _. by iFrame "HValues".
Qed.

Let impl := (SQSegment segment_size pointer_shift).

Theorem getCleanedAndPointersLoc_spec γ node:
  {{{ is_node γ node }}}
    getCleanedAndPointersLoc impl node
  {{{ cℓ, RET #cℓ; has_value cleanedAndPointers_uniqueValue γ cℓ }}}.
Proof.
  iIntros (Φ) "#HNode HΦ".
  iDestruct "HNode" as (ℓ -> values) "#(HInv & HValues & #HHeapInv & HLoc)".
  wp_lam. wp_bind (! _)%E.
  iMod (inv_mapsto_acc with "HHeapInv HLoc") as (?) "(-> & Hℓ & HℓRestore)";
    first done.
  wp_load. iMod ("HℓRestore" with "Hℓ") as "_". iModIntro. wp_pures.
  iApply "HΦ". iExists _. by iFrame "HValues".
Qed.

Theorem getId_spec γ node:
  {{{ is_node γ node }}}
    getId impl node
  {{{ id, RET #id; has_value id_uniqueValue γ id }}}.
Proof.
  iIntros (Φ) "#HNode HΦ".
  iDestruct "HNode" as (ℓ -> values) "#(HInv & HValues & #HHeapInv & HLoc)".
  wp_lam. wp_bind (! _)%E.
  iMod (inv_mapsto_acc with "HHeapInv HLoc") as (?) "(-> & Hℓ & HℓRestore)";
    first done.
  wp_load. iMod ("HℓRestore" with "Hℓ") as "_". iModIntro. wp_pures.
  iApply "HΦ". iExists _. by iFrame "HValues".
Qed.

Theorem node_unboxed γ node:
  is_node γ node -∗ ⌜val_is_unboxed node⌝.
Proof. iIntros "#HNode". by iDestruct "HNode" as (ℓ ->) "_". Qed.

Theorem node_induces_id γ γ' node id id':
  has_value id_uniqueValue γ id -∗
  has_value id_uniqueValue γ' id' -∗
  is_node γ  node -∗
  is_node γ' node ==∗
  ⌜id = id'⌝.
Proof.
  iIntros "HId HId' HNode HNode'".
  iDestruct "HNode" as (ℓ -> values) "#(HInv & HValues & #HHeapInv & HLoc)".
  iDestruct "HNode'" as (ℓ' HEq values') "#(HInv' & HValues' & #HHeapInv' & HLoc')".
  iDestruct "HId" as (?) "[HId <-]". iDestruct "HId'" as (?) "[HId' <-]".
  iDestruct (has_value_agrees with "HId HValues") as "->".
  iDestruct (has_value_agrees with "HId' HValues'") as "->".
  iDestruct (own_valid_2 with "HLoc HLoc'") as %HH.
  iPureIntro. move: HH.
  simplify_eq.
  rewrite -auth_frag_op auth_frag_valid.
  rewrite gmap.singleton_op gmap.singleton_valid pair_valid.
  case=>_/=HH.
  apply (@agree_op_inv' (option val -d> PropO)) in HH.
  specialize (HH (Some (#(segmentId values),
                        #(segmentCleanedAndPointersLocation values),
                        #(segmentPrevLocation values),
                        #(segmentNextLocation values),
                        #(segmentDataLocation values)))%V).
  simpl in *. inversion HH as [HH1 _]. specialize (HH1 eq_refl).
  destruct values; destruct values'; simpl in *. by simplify_eq.
Qed.

Instance cellStateDecidable (v v': cellState): Decision (v = v').
Proof. case v; case v'; by constructor. Defined.

Definition segment_content γ alive_slots: iProp :=
  ∃ values state,
    ⌜count_matching (fun v => v = cellAlive) state = alive_slots⌝ ∧
    own γ (algebra_from_list values state).

Theorem cancel_cell γ id alive_slots:
  cell_cancellation_handle γ id -∗
  segment_content γ alive_slots ==∗
  cell_is_cancelled γ id ∗ ∃ alive_slots',
      ⌜alive_slots = S alive_slots'⌝ ∧ segment_content γ alive_slots'.
Proof.
  iIntros "HHandle HContent". iDestruct "HContent" as (values state HCount) "Hγ".
  iAssert (⌜state !! id = Some cellAlive⌝)%I as %HLookup.
  {
    rewrite /algebra_from_list.
    iDestruct (own_valid_2 with "Hγ HHandle") as
        %[[(seg & HLookup & HIncluded)%list_singletonM_included
                                      _]%auth_both_valid _]%pair_valid.
    iPureIntro.
    rewrite map_lookup in HLookup.
    destruct (state !! id) as [state'|] eqn:HLookup'; last done.
    simpl in *. simplify_eq.
    destruct state'; first done.
    move: HIncluded=> /=. rewrite Some_included. case.
      + intros HContra. inversion HContra.
      + rewrite csum_included. case; first done.
        case; by intros (? & ? & ? & ? & ?).
  }
  destruct alive_slots as [|alive_slots'].
  { exfalso. move: HCount HLookup. clear. move: id.
    induction state as [|x xs]; first done. simpl.
    destruct x; simpl; first done. by case. }
  iMod (auth_cancel_cell with "HHandle Hγ") as "[Hγ $]".
  iExists alive_slots'. iSplitR; first done.
  iExists _, _. iFrame "Hγ". iPureIntro.
  rewrite list_insert_alter. erewrite count_matching_alter; last done.
  rewrite HCount /=. lia.
Qed.

Theorem newSegment_spec (id: nat) (prev: val) (pointers: nat):
  {{{ inv_heap_inv }}}
    newSegment impl #id prev #pointers
    {{{ γ node pℓ nℓ cℓ, RET node;
        is_node γ node
        ∗ segment_content γ (maxSlots impl)
        ∗ has_value id_uniqueValue γ id
        ∗ has_value cleanedAndPointers_uniqueValue γ cℓ
        ∗ has_value prev_uniqueValue γ pℓ
        ∗ has_value next_uniqueValue γ nℓ
        ∗ pℓ ↦ prev ∗ nℓ ↦ NONEV ∗ cℓ ↦ #(pointers ≪ pointerShift impl)
    }}}.
Proof.
  iIntros (Φ) "#HInv HΦ". wp_lam. wp_pures.
  wp_alloc dℓ as "Hdℓ"; first lia. wp_alloc nℓ as "Hnℓ".
  wp_alloc pℓ as "Hpℓ". wp_alloc cℓ as "Hcℓ".
  rewrite -wp_fupd.
  wp_alloc ℓ as "Hℓ".
  pose values := {|
      segmentId := id;
      segmentNextLocation := nℓ;
      segmentPrevLocation := pℓ;
      segmentCleanedAndPointersLocation := cℓ;
      segmentDataLocation := dℓ;
    |}.
  iMod (own_alloc (
            algebra_from_list values (replicate segment_size_nat cellAlive) ⋅
            (ε, Some (to_agree values)) ⋅
            (◯ replicate segment_size_nat
               (Some (cell_algebra_from_state cellAlive)), ε)))
    as (γ) "[[H● #HValues] HCancellation]".
  {
    rewrite /algebra_from_list -!pair_op /= pair_valid.
    split.
    - apply auth_both_valid. rewrite fmap_replicate.
      split; first done.
      apply list_lookup_valid=> i.
      destruct (_ !! i) eqn:E; last done.
      apply lookup_replicate in E. by destruct E as [-> _].
    - apply Some_valid. rewrite agree_idemp. done.
  }
  iApply "HΦ".
  replace (Z.pos pointer_shift) with (Z.of_nat (pointerShift impl));
    last by rewrite /impl /=; lia.
  iFrame "Hpℓ Hnℓ Hcℓ".
  iSplitL "Hℓ HCancellation Hdℓ"; last iSplitL "H●".
  - iExists _. iSplitR; first done. iExists values.
    iFrame "HInv HValues".
    iMod (make_inv_mapsto with "HInv Hℓ") as "Hℓ'"; first done;
      last iDestruct (inv_mapsto_own_inv with "Hℓ'") as "$"; first done.
    iMod (inv_alloc N _ (segment_invariant γ values) with "[-]") as "$";
      last done.
    rewrite /segment_invariant /segment_size_nat Z2Nat.inj_pos /array.
    iAssert ([∗ list] i ∈ seq 0 (Pos.to_nat segment_size),
             cell_cancellation_handle γ i)%I
      with "[HCancellation]" as "HCancellation".
    {
      rewrite /cell_cancellation_handle.
      iClear "HInv HValues".
      remember (Pos.to_nat segment_size) as n. clear.
      remember (Some _) as state. clear.
      replace (replicate _ _) with (replicate 0 ε ++ replicate n state);
        last done.
      remember 0 as start. clear.
      iInduction n as [|n'] "IH" forall (start); first done.
      simpl.
      assert ((replicate start ε ++ state :: replicate n' state)
                ≡ (replicate (S start) ε ++ replicate n' state) ⋅
                {[ start := state ]}) as ->.
      {
        replace (S start) with (start + 1) by lia.
        rewrite replicate_plus /= -app_assoc /=.
        apply list_equiv_lookup=> i. rewrite list_lookup_op.
        destruct (lt_eq_lt_dec i start) as [[HLt| ->]|HGt].
        - rewrite list_lookup_singletonM_lt; last lia.
          rewrite !lookup_app_l; try rewrite replicate_length //.
          by rewrite lookup_replicate_2; last lia.
        - rewrite list_lookup_singletonM.
          rewrite !lookup_app_r; try rewrite replicate_length //.
          rewrite Nat.sub_diag /=. rewrite -Some_op ucmra_unit_left_id //.
        - rewrite list_lookup_singletonM_gt; last lia.
          rewrite !lookup_app_r replicate_length; try lia.
          rewrite ucmra_unit_right_id.
          destruct (i - start) eqn:E; first lia. done.
      }
      rewrite auth_frag_op pair_op_1 own_op.
      iDestruct "HCancellation" as "[HCancellation $]".
      iApply ("IH" with "HCancellation").
    }
    assert (([∗ list] i ↦ v ∈ seq 0 (Pos.to_nat segment_size),
             (dℓ +ₗ i) ↦ InjLV #())%I ≡
            ([∗ list] i↦v ∈ replicate (Pos.to_nat segment_size) (InjLV #()),
              (dℓ +ₗ i) ↦ v)%I) as <-.
    {
      apply big_opL_gen_proper_2. done. by apply _.
      intros k.
      destruct (seq _ _ !! k) eqn:E.
      - apply lookup_seq in E. destruct E as [-> Hk].
        by rewrite lookup_replicate_2; last lia.
      - apply lookup_ge_None in E. rewrite seq_length in E.
        rewrite lookup_ge_None_2 // replicate_length. lia.
    }
    iCombine "Hdℓ" "HCancellation" as "H".
    rewrite -big_sepL_sep.
    iApply (big_sepL_mono with "H").
    intros ? ? HEq. apply lookup_seq in HEq. destruct HEq as [-> Hk].
    iIntros "[Hdℓ HCancHandle]". iRight. iFrame.
  - rewrite /segment_content. iExists values, _. iFrame "H●".
    iPureIntro. rewrite /impl /segment_size_nat /=.
    remember (Pos.to_nat _) as listLen. clear.
    induction listLen; first done. rewrite /= IHlistLen //.
  - repeat iSplitR; iExists _; iFrame "HValues"; done.
Qed.

Lemma max_slots_bound: (0 < maxSlots impl < 2 ^ pointerShift impl)%nat.
Proof. rewrite /impl /=. split; first lia; last done. Qed.

End infinite_array_segment_proof.

Require Import SegmentQueue.lib.concurrent_linked_list.list_interfaces.

Section segment_specs.

Variable (segment_size pointer_shift: positive).
Variable (limit: Pos.to_nat segment_size < 2 ^ Pos.to_nat pointer_shift).
Variable (N: namespace).

Definition node_linkedListNode `{!heapG Σ} `{!iSegmentG Σ}:
  linkedListNodeSpec Σ (base (SQSegment segment_size pointer_shift)) :=
  {| segment_spec.getPrevLoc_spec := getPrevLoc_spec segment_size N;
     segment_spec.getNextLoc_spec := getNextLoc_spec segment_size N;
     segment_spec.linkedListNode_unboxed := node_unboxed segment_size N;
     segment_spec.is_linkedListNode_persistent :=
       is_node_persistent segment_size N;
  |}.

Canonical Structure node_segment `{!heapG Σ}
          `{!iSegmentG Σ}: segmentSpec Σ (SQSegment segment_size pointer_shift)
  := {|
  segment_spec.linkedListNode_base := node_linkedListNode;
  segment_spec.getId_spec :=
    getId_spec segment_size pointer_shift N;
  segment_spec.getCleanedAndPointersLoc_spec :=
    getCleanedAndPointersLoc_spec segment_size pointer_shift N;
  segment_spec.newSegment_spec :=
    newSegment_spec segment_size pointer_shift N;
  segment_spec.max_slots_bound :=
    max_slots_bound segment_size pointer_shift limit;
  segment_spec.node_induces_id :=
    node_induces_id segment_size N;
  |}.

Variable list_impl: listInterface.

Definition newInfiniteArray: val :=
  newList list_impl.

Definition cancelCell: val :=
  λ: "ptr", onSlotCleaned list_impl (Snd "ptr").

Definition findCell: val :=
  λ: "ptr" "id",
  let: "sid" := "id" `rem` #(Pos.to_nat segment_size) in
  let: "cid" := "id" `quot` #(Pos.to_nat segment_size) in
  let: "seg" := findSegment list_impl (Fst "ptr") "sid" in
  if: getId (SQSegment segment_size pointer_shift) "seg" = "sid" then
    if: "cid" < Snd "ptr" then "ptr" else ("seg", "cid")
  else ("seg", #0).

Definition derefCellPointer: val :=
  λ: "ptr", let: "seg" := Fst "ptr" in
            let: "ix" := Snd "ptr" in
            getDataLoc "seg" +ₗ "ix".

Definition cellPointerCleanPrev: val :=
  λ: "ptr", cleanPrev list_impl (Fst "ptr").

Definition cutoffMoveForward: val :=
  λ: "cutoff" "ptr", moveForward list_impl "cutoff" (Fst "ptr").

Definition cutoffGetPointer: val :=
  λ: "cutoff", (!"cutoff", #0).

End segment_specs.

Require Import SegmentQueue.lib.concurrent_linked_list.list_spec.

Section array_impl.

Context `{heapG Σ} `{iSegmentG Σ}.

Variable (segment_size pointer_shift: positive).
Variable (limit: Pos.to_nat segment_size < 2 ^ Pos.to_nat pointer_shift).
Variable (N: namespace).
Variable list_impl: listInterface.
Variable list_spec: listSpec Σ list_impl
                             (node_segment segment_size pointer_shift limit N).

Definition is_infinite_array γ
           (cell_is_owned: nat -> iProp Σ) :=
  is_concurrentLinkedList _ _ _ list_spec N cell_is_owned γ.

Global Instance is_infinite_array_persistent γ cell_is_owned:
  Persistent (is_infinite_array γ cell_is_owned).
Proof. apply _. Qed.

Let segment_size_nat := Pos.to_nat segment_size.

Definition segment_view γ i f: iProp Σ :=
  ∃ γs v, segment_in_list _ _ _ list_spec γ γs (i `div` segment_size_nat) v ∗
          f γs (i `mod` segment_size_nat) v.

Definition infinite_array_mapsto γ i ℓ: iProp Σ :=
  segment_view γ i (fun γs ix v =>
  ∃ dℓ, has_value dataLocation_uniqueValue γs dℓ ∗ ⌜ℓ = dℓ +ₗ ix⌝)%I.

Global Instance infinite_array_mapsto_persistent γ i ℓ:
  Persistent (infinite_array_mapsto γ i ℓ).
Proof. apply _. Qed.

Theorem infinite_array_mapsto_agree γ i ℓ ℓ':
  infinite_array_mapsto γ i ℓ -∗ infinite_array_mapsto γ i ℓ' -∗ ⌜ℓ = ℓ'⌝.
Proof.
  iIntros "H1 H2". rewrite /infinite_array_mapsto.
  iDestruct "H1" as (? ?) "(H1 & H1Rest)".
  iDestruct "H2" as (? ?) "(H2 & H2Rest)".
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

Definition is_infinite_array_cutoff γ (v: val) (i: nat): iProp Σ :=
  ∃ (ℓ: loc), ⌜v = #ℓ⌝ ∧ segment_view γ i (fun γs ix v => ℓ ↦ v).

Definition cell_is_cancelled' γ i: iProp Σ :=
  segment_view γ i (fun γs ix v => cell_is_cancelled γs ix).

Global Instance cell_is_cancelled'_persistent γ i:
  Persistent (cell_is_cancelled' γ i).
Proof. apply _. Qed.

Definition cell_cancellation_handle' γ i: iProp Σ :=
  segment_view γ i (fun γs ix v => cell_cancellation_handle γs ix).

Theorem cell_cancellation_handle'_exclusive γ i:
  cell_cancellation_handle' γ i -∗ cell_cancellation_handle' γ i -∗ False.
Proof.
  iIntros "H1 H2". rewrite /infinite_array_mapsto.
  iDestruct "H1" as (? ?) "(H1 & H1Rest)".
  iDestruct "H2" as (? ?) "(H2 & H2Rest)".
  iDestruct (segment_in_list_agree with "H1 H2") as "[-> ->]".
  iDestruct (cell_cancellation_handle_exclusive with "H1Rest H2Rest") as %[].
Qed.

Theorem cell_cancellation_handle'_not_cancelled γ i:
  cell_is_cancelled' γ i -∗ cell_cancellation_handle' γ i -∗ False.
Proof.
  iIntros "H1 H2". rewrite /infinite_array_mapsto.
  iDestruct "H1" as (? ?) "(H1 & H1Rest)".
  iDestruct "H2" as (? ?) "(H2 & H2Rest)".
  iDestruct (segment_in_list_agree with "H1 H2") as "[-> ->]".
  iDestruct (cell_with_handle_not_cancelled with "H1Rest H2Rest") as %[].
Qed.

Theorem acquire_cell γ cell_is_owned i ℓ:
    is_infinite_array γ cell_is_owned -∗
    infinite_array_mapsto γ i ℓ -∗
    ∀ Φ, (cell_is_owned i ∨ ℓ ↦ NONEV ∗ cell_cancellation_handle' γ i
    ={⊤∖↑N}=∗ cell_is_owned i ∗ Φ) ={↑N}=∗ Φ.
Proof.
  iIntros "#HArr #HMapsto" (Φ) "HΦ".
  iDestruct "HMapsto" as (? ?) "[HSeg HRest]".
  rewrite /is_infinite_array.
  iMod (access_segment _ _ _ list_spec _ _ false with "HArr HSeg [% //]")
    as (n) "(_ & HSegContent & HRestore)"; first done.
  rewrite /segment_content /= /array_impl.segment_content /=.
Abort.

End array_impl.

(*
      cancelCell_spec N γ co p i:
        is_infinite_array N γ co -∗
        is_infinite_array_cell_pointer γ p i -∗
        <<< cell_cancellation_handle γ i >>>
            cancelCell p @ ⊤
        <<< cell_is_cancelled γ i, RET #() >>>;
      findCell_spec N γ co p (source_id id: nat):
        {{{ is_infinite_array N γ co ∗
            is_infinite_array_cell_pointer γ p source_id }}}
        findCell p #id @ ⊤
        {{{ p' id', RET p'; is_infinite_array_cell_pointer γ p' id'
            ∗ (⌜source_id <= id <= id'⌝ ∨
              ⌜source_id > id ∧ id' = source_id⌝)%nat
            ∗ [∗ list] i ∈ seq id (id' - id), cell_is_cancelled γ i
        }}};
      derefCellPointer_spec γ (p: val) i:
        {{{ is_infinite_array_cell_pointer γ p i }}}
          derefCellPointer p
        {{{ ℓ, RET #ℓ; infinite_array_mapsto γ i ℓ }}};
      cutoffMoveForward_spec γ (p v: val) i:
        is_infinite_array_cell_pointer γ p i -∗
        <<< ∀ start_index, ▷ is_infinite_array_cutoff γ v start_index >>>
          cutoffMoveForward v p @ ⊤
        <<< ∃ (success: bool), if success
            then ∃ i', ⌜start_index ≤ i' ≤ i⌝ ∧ is_infinite_array_cutoff γ v i'
            else ▷ is_infinite_array_cutoff γ v start_index ∗
                cell_is_cancelled γ start_index, RET #success >>>;
      cutoffGetPointer_spec γ (v: val):
        ⊢ <<< ∀ i, ▷ is_infinite_array_cutoff γ v i >>>
          cutoffGetPointer v @ ⊤
        <<< ∃ (p: val), is_infinite_array_cutoff γ v i ∗
                        is_infinite_array_cell_pointer γ p i, RET p >>>
 *)
