From iris.program_logic Require Import atomic.
From iris.algebra Require Import cmra auth list agree csum numbers.
From iris.base_logic Require Import lib.invariants.
From SegmentQueue.lib.concurrent_linked_list
     Require Export segment_spec list_spec list_impl.
Require Import SegmentQueue.util.everything.
Open Scope nat.

Section concurrentLinkedListProof.

Context `{heapG Σ}.
Context {segment_interface: segmentInterface}.
Variable segment_spec: (segmentSpec Σ segment_interface).
Let segment_size := maxSlots segment_interface.
Let segment_name := linkedListNode_name
                      _ _ (linkedListNode_base _ _ segment_spec).

Notation segment_contents_algebra :=
  (optionUR (csumR
               (* the segment was cancelled *)
               (agreeR unitO)
               (* the number of existing obligations (pointers, alive cells): *)
               positiveR)).

Notation segment_algebra :=
  (prodUR (optionUR (agreeR (leibnizO segment_name))) segment_contents_algebra).

Notation algebra := (authUR (listUR segment_algebra)).

Instance algebra_discrete: ∀ (x: algebra), Discrete x.
Proof. apply _. Qed.

Class iLinkedListG Σ := ILinkedListG { iLinkedList_inG :> inG Σ algebra }.
Definition iLinkedListΣ : gFunctors := #[GFunctor algebra].
Instance subG_iLinkedListΣ : subG iLinkedListΣ Σ → iLinkedListG Σ.
Proof. solve_inG. Qed.
Context `{iLinkedListG Σ}.

Notation iProp := (iProp Σ).

Variable (N: namespace).

Section segment_state.

  Definition segment_is_pointed_to (γ: gname) (id: nat): iProp :=
    own γ (◯ {[ id := (ε, Some (Cinr 1%positive)) ]}).

  Definition segment_has_slots := segment_is_pointed_to.

  Definition segment_is_cancelled (γ: gname) (id: nat): iProp :=
    own γ (◯ {[ id := (ε, Some (Cinl (to_agree tt))) ]}).

  Global Instance segment_is_cancelled_persistent γ id:
    Persistent (segment_is_cancelled γ id).
  Proof. apply _. Qed.

  Theorem segment_is_pointed_to_not_cancelled: ∀ γ id,
      segment_is_cancelled γ id -∗ segment_is_pointed_to γ id -∗ False.
  Proof.
    iIntros (γ id) "#HCanc HPointed".
    iDestruct (own_valid_2 with "HCanc HPointed") as %HValid.
    iPureIntro.
    move: HValid.
    rewrite -auth_frag_op auth_frag_valid list_singletonM_op list_singletonM_valid.
    by case.
  Qed.

  Definition segment_has_slots_not_cancelled :=
    segment_is_pointed_to_not_cancelled.

End segment_state.

Definition segment_name_uniqueValue (γ: gname):
  @uniqueValue Σ nat (leibnizO segment_name).
Proof.
  eapply UniqueValue with
      (has_value :=
         (fun id γs => own γ (◯ {[ id := (Some (to_agree γs), ε) ]}))).
  - intros. apply own_core_persistent, _.
  - intros. apply own_timeless, _.
  - iIntros (id v1 v2) "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %HValid.
    iPureIntro.
    move: HValid.
    rewrite -auth_frag_op list_singletonM_op auth_frag_valid list_singletonM_valid.
    case. rewrite /= -Some_op Some_valid=> HAgree.
    by apply agree_op_invL' in HAgree.
Defined.

Definition segment_in_list γ γs id node: iProp :=
  has_value (segment_name_uniqueValue γ) id γs
  ∗ has_value (id_uniqueValue _ _ _) γs id
  ∗ is_linkedListNode _ _ _ γs node.

Global Instance segment_in_list_persistent γ γs id ptr:
  Persistent (segment_in_list γ γs id ptr).
Proof. apply _. Qed.

Definition segment_algebra_from_state (γs: leibnizO segment_name)
           (pointers slots: nat): segment_algebra :=
  (Some (to_agree γs),
   Some (if decide (pointers = 0 ∧ slots = 0)
         then Cinl (to_agree tt)
         else Cinr (Pos.of_nat
                      (pointers + match slots with 0 => 0 | S _ => 1 end)))).

Section cleanedAndPointers_pure.

  Definition cleanedAndPointers_contents (pointers slots: nat): nat :=
    pointers * 2 ^ pointerShift segment_interface +
                  (maxSlots segment_interface - slots).

  Lemma cleanedAndPointers_contents_zero:
    cleanedAndPointers_contents 0 0 = maxSlots segment_interface.
  Proof. rewrite /cleanedAndPointers_contents. lia. Qed.

  Lemma cleanedAndPointers_contents_nonzero pointers slots:
    (pointers ≠ 0 ∨ slots ≠ 0) →
    cleanedAndPointers_contents pointers slots ≠ maxSlots segment_interface.
  Proof.
    rewrite /cleanedAndPointers_contents.
    move: (max_slots_bound _ _ segment_spec).
    case pointers.
    by rewrite Nat.mul_0_l; lia.
    lia.
  Qed.

End cleanedAndPointers_pure.

Definition is_segment (γ: gname) (is_tail: bool) (id: nat)
           (γs: segment_name) (pointers slots: nat): iProp :=
  (segment_content _ _ _ γs slots ∗
   match slots with | 0 => True | S _ => segment_has_slots γ id end)
  ∗ (∃ node, is_linkedListNode _ _ _ γs node)
  ∗ has_value (id_uniqueValue _ _ _) γs id
  ∗ (∃ cℓ, has_value (cleanedAndPointers_uniqueValue _ _ _) γs cℓ
            ∗ cℓ ↦ #(cleanedAndPointers_contents pointers slots))
  ∗ (∃ pℓ, has_value (prev_uniqueValue _ _ _) γs pℓ
            ∗ (pℓ ↦ NONEV ∨
              (∃ (pid: nat) (ptr: val),
                  (∃ γsp, segment_in_list γ γsp pid ptr)
                                  ∗ ⌜(pid < id)%nat⌝
                                  ∗ (∀ cid, ⌜(pid < cid < id)%nat⌝ -∗
                                            segment_is_cancelled γ cid)
                                  ∗ pℓ ↦ SOMEV ptr)))
  ∗ (∃ nℓ, has_value (next_uniqueValue _ _ _) γs nℓ
            ∗ if is_tail
              then nℓ ↦ InjLV #()
              else (∃ (nid: nat) (ptr: val),
                        (∃ γsn, segment_in_list γ γsn nid ptr)
                        ∗ ⌜(id < nid)%nat⌝
                        ∗ (∀ cid, ⌜(id < cid < nid)%nat⌝ -∗
                                  segment_is_cancelled γ cid)
                        ∗ nℓ ↦ SOMEV ptr))
  ∗ ⌜slots ≤ maxSlots segment_interface⌝.

Notation list_state := (list (leibnizO segment_name * (nat * nat))).

Definition auth_ra (state: list_state) :=
  ● @fmap list list_fmap _ _
    (fun p => match p with
                (γs, (pointers, slots)) =>
                segment_algebra_from_state γs pointers slots
              end) state.

Definition concurrentLinkedList_invariant (γ: gname): iProp :=
  ∃ (state: list_state), own γ (auth_ra state) ∗ [∗ list] id ↦ p ∈ state,
  match p with
    (γs, (pointers, slots)) =>
    is_segment γ (length state =? S id) id γs pointers slots
  end.

Lemma concurrentLinkedList_lookup_auth_ra state γ id s:
  own γ (◯ {[ id := s ]}) -∗
  own γ (auth_ra state) -∗
  ∃ γs pointers slots,
    ⌜s ≼ segment_algebra_from_state γs pointers slots ∧
    state !! id = Some (γs, (pointers, slots))⌝.
Proof.
  iIntros "HFrag HAuth".
  iDestruct (own_valid_2 with "HAuth HFrag") as
      %[(segment_params & HMapElem & HAgree)
          %list_singletonM_included _]
       %auth_both_valid.
  iPureIntro.
  rewrite list_lookup_fmap in HMapElem.
  destruct (state !! id) as [[p1 [p2 p3]]|]; simpl in *; simplify_eq.
  eauto.
Qed.

Section not_tail.

  Definition segment_is_not_tail γ id: iProp :=
    own γ (◯ {[ S id := ε ]}).

  Lemma not_tail_not_end_of_list state γ id:
    segment_is_not_tail γ id -∗
    own γ (auth_ra state) -∗
    ⌜(S id < length state)%nat⌝.
  Proof.
    iIntros "HNotTail HAuth".
    iDestruct (concurrentLinkedList_lookup_auth_ra with "HNotTail HAuth")
              as %(? & ? & ? & ? & HLookup).
    iPureIntro. by eapply lookup_lt_Some.
  Qed.

End not_tail.

Lemma concurrentLinkedList_insert γ γs id:
  has_value (segment_name_uniqueValue γ) id γs -∗
  concurrentLinkedList_invariant γ -∗
  (∃ list pointers slots,
      ⌜list !! id = Some (γs, (pointers, slots))⌝ ∗
      is_segment γ (length list =? S id) id γs pointers slots ∗
      own γ (auth_ra list) ∗
      ((∃ pointers' slots',
           is_segment γ (length list =? S id) id γs pointers' slots' ∗
          own γ (auth_ra (<[ id := (γs, (pointers', slots')) ]> list)))
         -∗ concurrentLinkedList_invariant γ)).
Proof.
  iIntros "Hγs HInv".
  iDestruct "HInv" as (s) "[Hγ HSegments]".
  iDestruct (concurrentLinkedList_lookup_auth_ra with "Hγs Hγ")
    as %(γs' & pointers & slots & [HAgree _]%pair_included & HLookup).
  move: HAgree. rewrite Some_included_total to_agree_included.
  intros HEquiv. apply leibniz_equiv in HEquiv. move: HEquiv. intros <-.
  iDestruct (big_sepL_insert_acc with "HSegments") as "[HSeg HRestore]";
    first done.
  iExists s, _, _. iFrame "HSeg Hγ". iSplitR; first by iPureIntro.
  iIntros "HNew". iDestruct "HNew" as (pointers' slots') "[HSeg Hγ]".
  iExists _. iFrame "Hγ".
  rewrite insert_length.
  by iApply "HRestore".
Qed.

Lemma concurrentLinkedList_insert_known_removed (known_is_removed: bool) γ γs id:
  has_value (segment_name_uniqueValue γ) id γs -∗
  (if known_is_removed then segment_is_cancelled γ id else True) -∗
  concurrentLinkedList_invariant γ -∗
  (∃ list pointers slots,
      ⌜list !! id = Some (γs, (pointers, slots))⌝ ∗
      ⌜known_is_removed = false ∨ (pointers = 0 ∧ slots = 0)⌝ ∗
      is_segment γ (length list =? S id) id γs pointers slots ∗
      own γ (auth_ra list) ∗
      ((∃ pointers' slots',
           is_segment γ (length list =? S id) id γs pointers' slots' ∗
          own γ (auth_ra (<[ id := (γs, (pointers', slots')) ]> list)))
         -∗ concurrentLinkedList_invariant γ)).
Proof.
  iIntros "Hγs HKnownRemoved HInv".
  iDestruct (concurrentLinkedList_insert with "Hγs HInv")
            as (list pointers slots HLookup) "(HSeg & Hγ & HRestore)".
  iExists list, pointers, slots.
  iSplitR; first done.
  destruct (decide (pointers = 0 ∧ slots = 0)) as [[-> ->]| HNEq].
  - iSplitR. by iPureIntro; right.
    iFrame "Hγ HSeg HRestore".
  - destruct known_is_removed.
    * iDestruct (own_valid_2 with "Hγ HKnownRemoved")
        as %[(? & HLookup' & [_ HIncluded]%pair_included)
               %list_singletonM_included _]%auth_both_valid.
      exfalso.
      rewrite map_lookup HLookup /= in HLookup'.
      simplify_eq.
      move: HIncluded. rewrite /segment_algebra_from_state.
      rewrite Some_included decide_False; last lia.
      case.
      by intros HContra; inversion HContra.
      rewrite csum_included. case; first done.
      case.
      by intros (? & ? & _ & HContra & _); inversion HContra.
      by intros (? & ? & HContra & _ & _); inversion HContra.
    * iSplitR. by iPureIntro; left.
      iFrame "Hγ HSeg HRestore".
Qed.

Lemma concurrentLinkedList_lookup_acc γ γs id:
  has_value (segment_name_uniqueValue γ) id γs -∗
  concurrentLinkedList_invariant γ -∗
  (∃ is_tail pointers slots,
      is_segment γ is_tail id γs pointers slots ∗
      (is_segment γ is_tail id γs pointers slots
         -∗ concurrentLinkedList_invariant γ)).
Proof.
  iIntros "Hγs HInv".
  iDestruct (concurrentLinkedList_insert with "Hγs HInv")
    as (list pointers slots HLookup) "(HIsSeg & HAuth & HRestore)".
  iExists (length list =? S id), pointers, slots. iFrame "HIsSeg".
  iIntros "HIsSeg". iApply "HRestore".
  iExists pointers, slots.
  rewrite list_insert_id; last done. by iFrame.
Qed.

Lemma concurrentLinkedList_lookup_acc_known_removed
      (known_is_removed: bool) γ γs id:
  has_value (segment_name_uniqueValue γ) id γs -∗
  (if known_is_removed then segment_is_cancelled γ id else True) -∗
  concurrentLinkedList_invariant γ -∗
  (∃ is_tail pointers slots,
      ⌜known_is_removed = false ∨ (pointers = 0 ∧ slots = 0)⌝ ∗
      is_segment γ is_tail id γs pointers slots ∗
      (is_segment γ is_tail id γs pointers slots
         -∗ concurrentLinkedList_invariant γ)).
Proof.
  iIntros "Hγs HKnownRemoved HInv".
  iDestruct (concurrentLinkedList_insert_known_removed known_is_removed
               with "Hγs HKnownRemoved HInv")
    as (list pointers slots HLookup HR) "(HIsSeg & HAuth & HRestore)".
  iExists (length list =? S id), pointers, slots. iFrame "HIsSeg".
  iSplitR; first done.
  iIntros "HIsSeg". iApply "HRestore".
  iExists pointers, slots.
  rewrite list_insert_id; last done. by iFrame.
Qed.


Definition is_concurrentLinkedList (γ: gname): iProp :=
  inv N (concurrentLinkedList_invariant γ) ∗
  initialization_requirements _ _ segment_spec.

Lemma getIsRemoved_spec (known_is_removed: bool) γ γs id v:
  {{{ inv N (concurrentLinkedList_invariant γ) ∗ segment_in_list γ γs id v ∗
      if known_is_removed then segment_is_cancelled γ id else True }}}
    getIsRemoved segment_interface v
  {{{ (v: bool), RET #v; if v then segment_is_cancelled γ id
                              else ⌜known_is_removed = false⌝ }}}.
Proof.
  iIntros (Φ) "(#HList & #HSeg & HKnownRemoved) HΦ".
  iDestruct "HSeg" as "(Hγs' & HId & HNode)".
  wp_lam.
  wp_apply (getCleanedAndPointersLoc_spec with "HNode").
  iIntros (cℓ) "#HValcℓ".
  wp_bind (!_)%E.

  iInv N as "HInv" "HClose".
  iDestruct (concurrentLinkedList_insert_known_removed known_is_removed
               with "Hγs' HKnownRemoved HInv")
    as (list pointers slots) "(>HLookup & >HR & HSeg & Hγ & HRestore)".
  iDestruct "HLookup" as %HLookup. iDestruct "HR" as %HR.
  iDestruct "HSeg" as "(HContent & HNode' & HId' & Hcℓ & HRest)".
  iDestruct "Hcℓ" as (cℓ') "(>HValcℓ' & Hcℓ)".
  iDestruct (has_value_agrees with "HValcℓ HValcℓ'") as %<-.

  wp_load.

  iAssert (is_segment γ (length list =? S id) id γs pointers slots ∗
          own γ (auth_ra list) -∗
          concurrentLinkedList_invariant γ)%I with "[HRestore]" as "HRestore".
  { iIntros "[HSeg Hγ]". iApply "HRestore". iExists pointers, slots.
    rewrite list_insert_id; last done. iFrame. }

  destruct (decide (pointers = 0 ∧ slots = 0)) as [[-> ->]|HNotRemoved].
  - iAssert (|==> own γ (auth_ra list) ∗ segment_is_cancelled γ id)%I with "[Hγ]"
      as ">[Hγ #HCancelled]".
    {
      iMod (own_update with "Hγ") as "[Hγ HCancelled]";
        first apply auth_update_core_id;
        last by iFrame.
      - apply _.
      - apply list_singletonM_included. rewrite list_lookup_fmap HLookup /=.
        eexists. split; first done. apply prod_included. rewrite /=; split.
        + apply ucmra_unit_least.
        + done.
    }
    iMod ("HClose" with "[-HΦ]") as "_".
    { iApply "HRestore". iFrame. iExists cℓ. by iFrame. }

    iModIntro. wp_pures. iApply "HΦ". rewrite bool_decide_true.
    by iFrame "HCancelled".
    by rewrite cleanedAndPointers_contents_zero.
  - destruct known_is_removed; first by destruct HR; simplify_eq.
    iMod ("HClose" with "[-HΦ]") as "_".
    { iApply "HRestore". iFrame. iExists cℓ. by iFrame. }

    iModIntro. wp_pures. iApply "HΦ".
    rewrite bool_decide_false //.
    case. intros HContra. apply Nat2Z.inj in HContra.
    by apply (cleanedAndPointers_contents_nonzero pointers slots); first lia.
Qed.

Lemma getPrev_spec γ γs id v:
  {{{ inv N (concurrentLinkedList_invariant γ) ∗ segment_in_list γ γs id v }}}
    getPrev (base segment_interface) v
  {{{ r, RET r; ⌜r = NONEV⌝ ∨
                ∃ (id': nat) (v': val),
                  ⌜r = SOMEV v' ∧ (id' < id)%nat⌝ ∧
                  (∃ γsp, segment_in_list γ γsp id' v') ∗
                  ∀ i, ⌜(id' < i < id)%nat⌝ -∗ segment_is_cancelled γ i
  }}}.
Proof.
  iIntros (Φ) "#[HList HSeg] HΦ".
  wp_lam. wp_bind (getPrevLoc _ _).
  iDestruct "HSeg" as "(Hγs & HId & HNode)".
  iApply (getPrevLoc_spec with "HNode").
  iIntros (pℓ) "!> #HValpℓ".
  iInv "HList" as "HOpen" "HClose".
  iDestruct (concurrentLinkedList_lookup_acc with "Hγs HOpen")
    as (? ? ?) "(HSeg & HRestore)".
  iDestruct "HSeg" as "(HContent & HNode' & HId' & Hcℓ & Hpℓ & HRest)".
  iDestruct "Hpℓ" as (pℓ') "[HValpℓ' Hpℓ]".
  iDestruct (has_value_agrees with "HValpℓ HValpℓ'") as "#><-".
  iDestruct "Hpℓ" as "[Hpℓ|Hpℓ]".
  2: iDestruct "Hpℓ" as (pid ptr) "(#HPSeg & >% & #HPCanc & Hpℓ)".
  all: wp_load.
  - iMod ("HClose" with "[-HΦ]") as "_"; first iApply "HRestore".
    { iFrame "HContent HNode' HId' Hcℓ HRest"; iExists pℓ; iFrame "HValpℓ".
      by iFrame "Hpℓ".
    }
    iApply "HΦ"; by iLeft.
  - iMod ("HClose" with "[-HΦ]") as "_"; first iApply "HRestore".
    { iFrame "HContent HNode' HId' Hcℓ HRest"; iExists pℓ; iFrame "HValpℓ".
      iRight. iExists pid, ptr. iFrame "HPSeg HPCanc Hpℓ". done.
    }
    iApply "HΦ"; iModIntro; iRight. iExists pid, ptr. repeat iSplitR; done.
Qed.

Lemma leftmostAliveNodeInternal_spec γ γs id v:
  {{{ inv N (concurrentLinkedList_invariant γ) ∗ segment_in_list γ γs id v }}}
    leftmostAliveNodeInternal segment_interface v
  {{{ r, RET r; ⌜r = NONEV⌝ ∨
                ∃ (id': nat) (v': val),
                  ⌜r = SOMEV v' ∧ (id' < id)%nat⌝ ∧
                  (∃ γsp, segment_in_list γ γsp id' v') ∗
                  ∀ i, ⌜id' < i < id⌝ -∗ segment_is_cancelled γ i }}}.
Proof.
  iIntros (Φ) "[#HList HSeg'] HΦ". wp_lam.
  remember id as start_id.
  iAssert (∀ i, ⌜id ≤ i < start_id⌝ -∗ segment_is_cancelled γ i)%I as "#HCanc";
    first by iIntros (? ?); lia.
  iAssert (segment_in_list γ γs id v) with "[HSeg']" as "#HSeg"; first by subst.
  assert (id ≤ start_id)%nat as HIdLeSId by lia.
  clear Heqstart_id. iClear "HSeg'".
  iLöb as "IH" forall (γs id v HIdLeSId) "HSeg HCanc".
  wp_bind (getPrev _ _). iApply (getPrev_spec with "[$]").
  iIntros (r) "!> Hr". iDestruct "Hr" as "[->|Hr]".
  - wp_pures. iApply "HΦ". iLeft. done.
  - iDestruct "Hr" as (id' v' [-> HLt]) "(#HSeg' & #HCanc')". wp_pures.
    iAssert (∀ i, ⌜id' < i < start_id⌝ -∗ segment_is_cancelled γ i)%I
      as "#HCanc''";
      first by iIntros (i ?); destruct (decide (id ≤ i));
        [iApply "HCanc"|iApply "HCanc'"]; iPureIntro; lia.
    iClear "HCanc HCanc'".
    wp_bind (getIsRemoved _ _).
    iDestruct "HSeg'" as (?) "HSeg'".
    iApply (getIsRemoved_spec false with "[$]").
    iIntros (r) "!> Hr".
    destruct r.
    + wp_pures.
      iApply ("IH" with "[%] HΦ HSeg' [#]"); first lia.
      iDestruct "Hr" as "#Hr". iIntros (i ?) "!>".
      destruct (decide (id' < i)).
      * iApply "HCanc''"; iPureIntro; lia.
      * assert (i = id') as -> by lia. iAssumption.
    + wp_pures. iApply "HΦ". iRight. iExists id', v'.
      iSplit. by iPureIntro; split; [done|lia].
      iSplit. by iExists _. done.
Qed.

Lemma later_segment_in_list_not_tail γ id id' s':
  (id < id')%nat → own γ (◯ {[ id' := s' ]}) -∗ segment_is_not_tail γ id.
Proof.
  iIntros (HLt) "HFrag". iApply (own_mono with "HFrag").
  apply auth_frag_mono, list_singletonM_included.
  destruct (decide (id' = S id)) as [->|HNe].
  - eexists. split; first by apply list_lookup_singletonM. apply ucmra_unit_least.
  - exists ε. split; last done. apply list_lookup_singletonM_lt. lia.
Qed.

Lemma getNext_spec (known_not_tail: bool) γ γs id v:
  {{{ inv N (concurrentLinkedList_invariant γ) ∗ segment_in_list γ γs id v ∗
      if known_not_tail then segment_is_not_tail γ id else True }}}
    ! (getNextLoc (base segment_interface) v)
  {{{ r, RET r; ⌜r = NONEV ∧ known_not_tail = false⌝ ∨
                ∃ id' v', ⌜r = SOMEV v' ∧ (id < id')%nat⌝ ∧
                          (∃ γsn, segment_in_list γ γsn id' v') ∗
                          ∀ i, ⌜id < i < id'⌝ -∗ segment_is_cancelled γ i }}}.
Proof.
  iIntros (Φ) "(#HList & #HSeg & HNotTail) HΦ".
  iDestruct "HSeg" as "(Hγs & HId & HNode)". wp_bind (getNextLoc _ _).
  iApply (getNextLoc_spec with "HNode"). iIntros (nℓ) "!> #HValnℓ".
  iInv "HList" as "HOpen" "HClose".
  iDestruct (concurrentLinkedList_insert with "Hγs HOpen")
    as (list pointers slots) "(>HLookup & HIsSeg & >Hγ & HRestore)".
  iDestruct "HLookup" as %HLookup.
  iDestruct "HIsSeg" as "(HContent & HNode' & HId'' & Hcℓ & Hpℓ & Hnℓ & HRest)".
  iDestruct "Hnℓ" as (current_nℓ) "(>HValnℓ' & Hnℓ)".
  iDestruct (has_value_agrees with "HValnℓ HValnℓ'") as %<-.
  destruct (decide (length list = S id)) as [HIsTail|HNotTail].
  - destruct known_not_tail.
    { iDestruct (own_valid_2 with "Hγ HNotTail")
        as %[[? [HValid _]]%list_singletonM_included _]%auth_both_valid.
      exfalso.
      apply list_lookup_fmap_inv in HValid.
      destruct HValid as [? [_ HLookup']].
      apply lookup_lt_Some in HLookup'. lia.
    }
    rewrite HIsTail Nat.eqb_refl.
    wp_load.
    iMod ("HClose" with "[-HΦ]") as "_".
    { iApply "HRestore". iExists pointers, slots.
      rewrite list_insert_id; last done.
      iFrame "HContent HNode' HId'' Hcℓ Hpℓ HRest Hγ".
      iExists nℓ. by iFrame. }
    iApply "HΦ". by iLeft.
  - iClear "HNotTail".
    apply Nat.eqb_neq in HNotTail. rewrite HNotTail.
    iDestruct "Hnℓ" as (nid nptr) "(#HNInList & >HCIdLtNId & #HTravCanc & Hnℓ)".
    iDestruct "HCIdLtNId" as %HCIdLtNId.
    wp_load.
    iMod ("HClose" with "[-HΦ]") as "_".
    { iApply "HRestore". iExists pointers, slots.
      rewrite list_insert_id; last done.
      iFrame. iExists nℓ. iFrame. iExists _, _. iFrame.
      iSplit; first iAssumption. iSplit; first by iPureIntro. done. }
    iApply "HΦ". iRight. iExists _, _.
    iFrame "HNInList HTravCanc". by iPureIntro.
Qed.

Lemma isTail_spec (known_not_tail: bool) γ γs id v:
  {{{ inv N (concurrentLinkedList_invariant γ) ∗ segment_in_list γ γs id v ∗
      if known_not_tail then segment_is_not_tail γ id else True }}}
    isTail (base segment_interface) v
  {{{ (r: bool), RET #r; if r then ⌜known_not_tail = false⌝
                              else segment_is_not_tail γ id }}}.
Proof.
  iIntros (Φ) "H HΦ". wp_lam. wp_lam. wp_pures. wp_lam. wp_pures.
  wp_bind (!_)%E. iApply (getNext_spec known_not_tail with "H").
  iIntros (r) "!> [[-> ->]|H]".
  - wp_pures. by iApply "HΦ".
  - iDestruct "H" as (? ? [-> ?]) "[H _]".
    wp_pures. iApply "HΦ". iDestruct "H" as (?) "(Hγ & _ & _)".
    by iDestruct (later_segment_in_list_not_tail with "Hγ") as "$".
Qed.

Lemma rightmostAliveNodeInternal_spec γ γs id v:
  {{{ inv N (concurrentLinkedList_invariant γ) ∗ segment_in_list γ γs id v ∗
      segment_is_not_tail γ id }}}
    rightmostAliveNodeInternal segment_interface v
  {{{ (id': nat) (v': val), RET v'; ⌜(id < id')%nat⌝ ∧
      (∃ γsn, segment_in_list γ γsn id' v') ∗
      ∀ i, ⌜id < i < id'⌝ -∗ segment_is_cancelled γ i
  }}}.
Proof.
  iIntros (Φ) "(#HList & #HSeg & #HNotTail) HΦ".
  wp_lam. wp_bind (isTail _ _).
  iApply (isTail_spec true with "[#]"); first by iFrame "HList HSeg HNotTail".
  iIntros (r) "!> Hr". destruct r; first by iDestruct "Hr" as %HContra.
  wp_pures.
  remember id as current_id. rewrite Heqcurrent_id.
  assert (id ≤ current_id)%nat as HIdLeCId by lia.
  iAssert (segment_in_list γ γs current_id v ∗ segment_is_not_tail γ current_id)%I
          with "[]" as "[HSeg' HNotTail']";
    first by subst; iFrame "HSeg HNotTail".
  iAssert (∀ i, ⌜id < i ≤ current_id⌝ -∗ segment_is_cancelled γ i)%I
          with "[]" as "#HCanc"; first by iIntros (? ?); lia.
  iClear "HSeg HNotTail Hr". clear Heqcurrent_id.
  iLöb as "IH" forall (current_id γs v HIdLeCId) "HΦ HSeg' HNotTail' HCanc".

  wp_lam. wp_pures. wp_lam. wp_pures. wp_bind (!_)%E.
  iApply (getNext_spec true with "[$]").
  iIntros (r) "!> [[_ %]|Hr]"; first done.
  iDestruct "Hr" as (id' v' [-> HCIdLtId']) "#[HNSeg HCanc']".
  wp_pures. wp_lam. wp_pures.

  iAssert (∀ i : nat, ⌜id < i ∧ i < id'⌝ -∗ segment_is_cancelled γ i)%I
          with "[]" as "#HCanc''".
  { iIntros (i Hi). destruct (decide (i ≤ current_id)%nat);
                      [iApply "HCanc"|iApply "HCanc'"]; iPureIntro; lia. }

  wp_bind (getIsRemoved _ _). iDestruct "HNSeg" as (?) "HNSeg".
  iApply (getIsRemoved_spec false with "[$]").
  iIntros (r) "!> Hr".
  destruct r; wp_pures.
  2: {
    iApply "HΦ". iSplit; last by [iSplit; first by iExists _|iAssumption].
    iPureIntro; lia.
  }
  iDestruct "Hr" as "#HId'Cancelled".
  wp_bind (isTail _ _). iApply (isTail_spec false with "[$]").
  iIntros (r') "!> Hr'".
  destruct r'; wp_pures.
  {
    iApply "HΦ". iSplit; last by [iSplit; first by iExists _|iAssumption].
    iPureIntro; lia.
  }
  iDestruct "Hr'" as "#HNotTail".
  iApply ("IH" with "[%] HΦ HNSeg HNotTail []"); first lia.
  iModIntro. iIntros (i ?).
  destruct (decide (i = id')) as [->|HNeq]; first done.
  iApply "HCanc''"; iPureIntro; lia.
Qed.

Lemma remove_spec γ γs id v:
  {{{ inv N (concurrentLinkedList_invariant γ) ∗ segment_in_list γ γs id v ∗
      segment_is_cancelled γ id }}}
    list_impl.remove segment_interface v
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "(#HList & #HSeg & #HCanc) HΦ". iSpecialize ("HΦ" with "[//]").
  wp_lam. wp_bind (getIsRemoved _ _). iApply (getIsRemoved_spec true with "[$]").
  iIntros (r). destruct r; last by iIntros (?). iIntros "!> _". wp_pures.
  wp_bind (isTail _ _). iApply (isTail_spec false with "[$]").
  iIntros (r).
  destruct r.
  { iIntros "!> _". wp_pures. by iApply "HΦ". }
  iIntros "!> #HNotTail". wp_pures. iLöb as "IH".

  wp_bind (leftmostAliveNodeInternal _ _).
  iApply (leftmostAliveNodeInternal_spec with "[$]").
  iIntros (prevv) "!> #HPrevVal". wp_pures.
  wp_bind (rightmostAliveNodeInternal _ _).
  iApply (rightmostAliveNodeInternal_spec with "[$]").
  iIntros (nextId nextv) "!> #HNextVal". wp_pures.
  iDestruct "HNextVal" as (HIdLtNextId) "[HNSeg HNCanc]".
  iDestruct "HNSeg" as (γsn) "(Hγsn & HNextId & HNextNode)".

  wp_bind (getPrevLoc _ _). iApply (getPrevLoc_spec with "HNextNode").
  iIntros (nextpℓ) "!> #HNextpℓVal".

  wp_bind (_ <- _)%E. iInv "HList" as "HOpen" "HClose".
  iDestruct (concurrentLinkedList_lookup_acc with "Hγsn HOpen")
    as (? ? ?) "(HNSeg & HRestore)".
  iDestruct "HNSeg" as "(HNContent & HNNode & HNextId' & HNcℓ & HNpℓ & HNRest)".
  iDestruct "HNpℓ" as (nextpℓ') "[HNextpℓVal' HNpℓ]".
  iDestruct (has_value_agrees with "HNextpℓVal HNextpℓVal'") as "><-".
  iAssert (∃ v, ▷ nextpℓ ↦ v)%I with "[HNpℓ]" as (?) "Hnpℓ".
  { iDestruct "HNpℓ" as "[HNpℓ|HNpℓ]"; first by iExists _.
    iDestruct "HNpℓ" as (? ?) "(? & ? & ? & HNpℓ)". by iExists _. }
  wp_store.
  iMod ("HClose" with "[-HΦ]") as "_".
  { iApply "HRestore". iFrame "HNContent HNNode HNextId' HNcℓ HNRest".
    iExists nextpℓ. iFrame "HNextpℓVal".
    iDestruct "HPrevVal" as "[->|HPrevVal]"; first by iLeft.
    iRight.
    iDestruct "HPrevVal" as (prevId prevv' [-> HLt]) "[HPSeg HPCanc]".
    iExists prevId, prevv'. iFrame "HPSeg Hnpℓ".
    iSplit; first by iPureIntro; lia.
    iIntros (i ?).
    destruct (lt_eq_lt_dec i id) as [[HLt'| -> ]|HGt].
    - iApply "HPCanc"; iPureIntro; lia.
    - iApply "HCanc".
    - iApply "HNCanc"; iPureIntro; lia.
  }

  iModIntro. wp_pures. wp_bind (Case _ _ _).
  iApply (wp_strong_mono NotStuck _ ⊤ _ _ (fun v => True)%I); [done|done| |].
  {
    iDestruct "HPrevVal" as "[->|HPrevVal]"; first by wp_pures.
    iDestruct "HPrevVal" as (prevId prevv' [-> HLt]) "[HPSeg HPCanc]".
    iDestruct "HPSeg" as (γsp) "(Hγsp & HPrevId & HPrevNode)".
    wp_pures.
    wp_bind (getNextLoc _ _). iApply (getNextLoc_spec with "HPrevNode").
    iIntros (prevnℓ) "!> HPrevnℓVal".

    iInv "HList" as "HOpen" "HClose".
    iDestruct (concurrentLinkedList_insert with "Hγsp HOpen")
      as (list ? ?) "(>HLookup & HPSeg & >Hγ & HRestore)".
    iDestruct "HLookup" as %HLookup.
    iDestruct (later_segment_in_list_not_tail _ prevId with "Hγsn")
      as "#HPNotTail"; first lia.
    iDestruct (not_tail_not_end_of_list with "HPNotTail Hγ") as %?.
    assert (length list ≠ S prevId) as HNeq by lia.
    apply Nat.eqb_neq in HNeq. rewrite HNeq.
    iDestruct "HPSeg" as
        "(HPContent & HPNode & HPrevId' & HPcℓ & HPpℓ & HPnℓ & HPRest)".
    iDestruct "HPnℓ" as (prevnℓ') "[#HPrevnℓVal' HPnℓ]".
    iDestruct (has_value_agrees with "HPrevnℓVal HPrevnℓVal'") as "><-".
    iDestruct "HPnℓ" as (? ?) "(_ & _ & _ & HPnℓ)".
    wp_store.

    iMod ("HClose" with "[-]"); last done.
    iApply "HRestore".
    iExists _, _. rewrite list_insert_id; last done. iFrame "Hγ".
    iFrame "HPContent HPNode HPrevId' HPcℓ HPpℓ HPRest".
    iExists prevnℓ. iFrame "HPrevnℓVal'". iExists nextId, nextv.
    iSplitR; first by iExists _; iFrame "Hγsn HNextId HNextNode".
    iSplitR; first by iPureIntro; lia.
    iSplitR; last by iAssumption.
    iIntros (i ?).
    destruct (lt_eq_lt_dec i id) as [[HLt'| -> ]|HGt].
    - iApply "HPCanc"; iPureIntro; lia.
    - iApply "HCanc".
    - iApply "HNCanc"; iPureIntro; lia.
  }

  iIntros (?) "_ !>". wp_pures. wp_bind (getIsRemoved _ _).
  iApply (getIsRemoved_spec false with "[]").
  by iFrame "HList"; iSplit; [iFrame "Hγsn HNextId HNextNode"|done].
  iIntros (r) "!> Hr".
  destruct r; wp_pures; first by iApply ("IH" with "HΦ").
  iDestruct "HPrevVal" as "[->|HPrevVal]"; first by wp_pures.
  iDestruct "HPrevVal" as (prevId prevv' [-> HLt]) "[HPSeg HPCanc]". wp_pures.
  wp_bind (getIsRemoved _ _).
  iDestruct "HPSeg" as (?) "HPSeg".
  iApply (getIsRemoved_spec false with "[]"). by iFrame "HList HPSeg".
  iIntros (r) "!> Hr'".
  destruct r; wp_pures; first by iApply ("IH" with "HΦ").
  iApply "HΦ".
Qed.

Lemma big_opL_take_drop_middle (M: ofeT) (o : M → M → M) (H': Monoid o) (A: Type)
      (f: nat → A → M) (l: list A) (id: nat) (x: A):
  l !! id = Some x →
  ([^o list] k ↦ y ∈ l, f k y) ≡
    (o ([^o list] k ↦ y ∈ take id l, f k y)
       (o (f id x) ([^o list] k ↦ y ∈ drop (S id) l, f (id + S k) y))).
Proof.
  intros HEl.
  erewrite <-(take_drop_middle l); last done.
  assert (id < length l)%nat by (eapply lookup_lt_Some; eassumption).
  rewrite big_opL_app take_app_alt.
  rewrite drop_app_ge.
  all: rewrite take_length_le //=; try lia.
  replace (S id - id)%nat with 1 by lia. simpl.
  by rewrite drop_0 Nat.add_0_r.
Qed.

Lemma trySetNext_spec γ γsp γs (v nv: val) (id: nat):
  {{{ inv N (concurrentLinkedList_invariant γ) ∗ segment_in_list γ γsp id v
      ∗ (segment_has_slots γ (S id) -∗
         is_segment γ true (S id) γs 0 (maxSlots segment_interface))
      ∗ has_value (id_uniqueValue _ _ _) γs (S id)
      ∗ is_linkedListNode _ _ _ γs nv }}}
    trySetNext (base segment_interface) v nv
  {{{ (r: bool), RET #r;
      if r then segment_in_list γ γs (S id) nv
           else (segment_has_slots γ (S id) -∗
                 is_segment γ true (S id) γs 0 (maxSlots segment_interface)) ∗
                ∃ nid, (∃ γsn ptr, segment_in_list γ γsn nid ptr) ∗ ⌜id < nid⌝ ∗
                       ∀ cid : nat, ⌜id < cid ∧ cid < nid⌝ -∗
                                    segment_is_cancelled γ cid }}}.
Proof.
  iIntros (Φ) "(#HList & #HSeg & HNSeg & #HNId & #HNNode) HΦ".
  wp_lam. wp_pures.
  wp_bind (getNextLoc _ _).
  iDestruct "HSeg" as "(Hγsp & HId & HNode)".
  iApply (getNextLoc_spec with "HNode").
  iIntros (nℓ) "!> #HValnℓ".
  wp_bind (CmpXchg _ _ _).
  iInv N as (list) "[Hγ HSegments]" "HClose".
  iDestruct (concurrentLinkedList_lookup_auth_ra with "Hγsp Hγ")
    as "#>HH".
  iDestruct "HH" as %(γs'' & pointers & slots &
                      [HIncluded _]%prod_included & HLookup).
  move: HIncluded. rewrite Some_included_total to_agree_included.
  move=> HEq. apply leibniz_equiv in HEq. subst γs''.
  rewrite big_opL_take_drop_middle; last done.
  rewrite /=.

  iDestruct "HSegments" as "(HSegmentsInit & HSegment & HSegmentsTail)".
  iDestruct "HSegment" as
      "(HContent & #HNode' & HId' & Hcℓ & Hpℓ & Hnℓ & HRest)".
  iDestruct "Hnℓ" as (nℓ') "(#>HValnℓ' & Hnℓ')".
  iDestruct (has_value_agrees with "HValnℓ HValnℓ'") as %<-.
  destruct (decide (length list = S id)) as [HIsTail|HNotTail].
  - iEval (rewrite HIsTail Nat.eqb_refl) in "Hnℓ'". iClear "HSegmentsTail".
    wp_cmpxchg_suc.
    pose new_list := list ++ [(γs, (0, maxSlots segment_interface))].
    (* Next, allocate the new segment in Hγ. *)
    iAssert (|==> own γ (auth_ra new_list) ∗
             has_value (segment_name_uniqueValue γ) (S id) γs ∗
             segment_has_slots γ (S id))%I
      with "[Hγ]" as ">(Hγ & #HNSegName & HNHasSlots)".
    {
      iMod (own_update with "Hγ") as "($ & $ & $)"; last done.
      apply auth_update_alloc.
      rewrite fmap_app /=.
      remember (fmap _ _) as l'.
      replace (S id) with (length l'); last by subst; rewrite map_length.
      rewrite /segment_algebra_from_state.
      move: (max_slots_bound _ _ segment_spec)=> HBound.
      rewrite decide_False; last lia.
      destruct (maxSlots _); first lia.
      rewrite /= list_singletonM_op -pair_op.
      by apply list_alloc_singletonM_local_update.
    }
    iSpecialize ("HNSeg" with "HNHasSlots").
    iAssert (segment_in_list γ γs (S id) nv) as "#HNListSeg";
      first by iFrame "HNSegName HNNode HNId".
    iAssert (is_segment γ false id γsp pointers slots)
      with "[HContent HId' Hcℓ Hpℓ Hnℓ' HRest]" as "HSegment".
    {
      iFrame "HContent HId' Hcℓ Hpℓ HNode' HRest". iExists nℓ.
      iFrame "HValnℓ". iExists (S id), nv.
      iSplitR. by iExists _. iFrame "Hnℓ'".
      iSplit; [iPureIntro|iIntros (? ?)]; lia.
    }
    iAssert ([∗ list] id ↦ p ∈ new_list,
             match p with
               (γs, (pointers, slots)) =>
               is_segment γ (length (new_list) =? S id) id γs pointers slots
             end)%I with "[HSegmentsInit HSegment HNSeg]" as "HSegments".
    {
      remember (take id list) as init_part.
      assert (list = init_part ++ [(γsp, (pointers, slots))]) as ->.
      {
        subst. replace nil with (drop (S id) list).
        by rewrite take_drop_middle.
        by rewrite drop_ge // HIsTail; lia.
      }
      rewrite app_length /= Nat.add_1_r in HIsTail. simplify_eq.
      clear HLookup Heqinit_part.
      rewrite take_app_le // firstn_all !big_sepL_app /=.
      rewrite !app_length !Nat.add_1_r !Nat.add_0_r Nat.eqb_refl.
      iEval (replace (_ =? _) with false by (symmetry; by apply Nat.eqb_neq)).
      iFrame "HSegment HNSeg".
      iApply (big_sepL_proper with "HSegmentsInit").
      intros k [? [? ?]] ?.
      assert (k < length init_part) as HEl
          by (eapply lookup_lt_Some; eassumption).
      move: HEl. remember (length init_part) as m. clear. move=> HEl.
      by repeat (replace (_ =? _) with false;
                 last (symmetry; apply Nat.eqb_neq; lia)).
    }
    iMod ("HClose" with "[Hγ HSegments]") as "_".
    by iExists new_list; iFrame.
    iModIntro. wp_pures. by iApply "HΦ".
  - apply Nat.eqb_neq in HNotTail.
    rewrite HNotTail.
    iDestruct "Hnℓ'" as (nid ptr) "(#H1 & #H2 & #H3 & Hnℓ)".
    wp_cmpxchg_fail.
    iMod ("HClose" with "[-HΦ HNSeg]") as "_".
    { iExists list. iFrame "Hγ".
      iEval (rewrite big_opL_take_drop_middle; last done).
      iFrame "HSegmentsInit HSegmentsTail".
      iFrame "HContent HId' Hcℓ Hpℓ HNode' HRest".
      iExists nℓ. iFrame "HValnℓ". rewrite HNotTail. iExists nid, ptr.
      iFrame "H1 H2 H3 Hnℓ".
    }

    iModIntro. wp_pures. iApply "HΦ". iFrame "HNSeg".
    iDestruct "H1" as (?) "H1".
    iExists nid; iFrame "H2 H3". by iExists _, _.
Qed.

Lemma list_newSegment_spec γ γs id pv (k: nat):
  {{{ ((∃ v, ⌜pv = SOMEV v⌝ ∧ segment_in_list γ γs id v) ∨ ⌜pv = NONEV⌝) ∗
      initialization_requirements _ _ segment_spec }}}
    newSegment segment_interface #(S id) pv #k
  {{{ γs v', RET v'; (segment_has_slots γ (S id) -∗
                      is_segment γ true (S id) γs k (maxSlots segment_interface))
                                ∗ has_value (id_uniqueValue _ _ _) γs (S id)
                                ∗ is_linkedListNode _ _ _ γs v' }}}.
Proof.
  iIntros (Φ) "[#HSegInList HInitReq] HΦ".
  iApply (newSegment_spec with "HInitReq").
  iIntros (nγs nnode npℓ nnℓ ncℓ) "!> HNext".
  iApply "HΦ".
  iDestruct "HNext" as "(#HNIsNode & HNContent & #HNId & HRest)".
  iFrame "HNContent HNIsNode HNId".
  iIntros "HHasSlots".
  iSplitL "HHasSlots".
  { destruct (maxSlots _). done. iFrame. }
  iSplit; first by iExists _.
  iDestruct "HRest" as "(#HValcℓ & #HValpℓ & #HValnℓ & Hpℓ & Hnℓ & Hcℓ)".
  iSplitL "Hcℓ"; last iSplitL "Hpℓ"; last iSplitL.
  - iExists ncℓ.
    replace (Z.shiftl _ _) with
        (Z.of_nat (cleanedAndPointers_contents k (maxSlots segment_interface))).
    by iFrame.
    rewrite /cleanedAndPointers_contents.
    rewrite Z.shiftl_mul_pow2; last by lia.
    replace 2%Z with (Z.of_nat 2) by lia.
    rewrite -Z2Nat_inj_pow Nat.sub_diag -Nat2Z.inj_mul.
    congr Z.of_nat. lia.
  - iExists npℓ.
    iFrame "HValpℓ".
    iDestruct "HSegInList" as "[HSegInList|->]".
    * iDestruct "HSegInList" as (v) "[-> HSegInList]".
      iRight. iExists id, v.
      iFrame "Hpℓ".
      repeat iSplit.
      + iExists _. by iFrame.
      + iPureIntro. lia.
      + iIntros (? HContra). lia.
    * by iLeft.
  - iExists nnℓ.
    by iFrame.
  - iPureIntro; lia.
Qed.

Theorem findSegmentInternal_spec γ γs' (start_id id: nat) v:
  {{{ is_concurrentLinkedList γ ∗ segment_in_list γ γs' start_id v }}}
    findSegmentInternal segment_interface v #id
  {{{ (v': val) (id': nat), RET (SOMEV v'); (∃ γs, segment_in_list γ γs id' v')
      ∗ ⌜(start_id ≤ id' ∧ id ≤ id')%nat⌝
      ∗ ∀ i, (⌜max start_id id ≤ i < id'⌝)%nat -∗ segment_is_cancelled γ i
  }}}.
Proof.
  iIntros (Φ) "#[[HList HInitReq] HSeg] HΦ".
  wp_lam. wp_pures.
  move HEqX: (start_id) => current_id.
  rewrite -HEqX.
  iEval (subst start_id) in "HSeg".
  iAssert (∀ i, (⌜max start_id id ≤ i < current_id⌝)%nat -∗
          segment_is_cancelled γ i)%I with "[]" as "#HCancelled".
  { subst. iIntros (? ?). lia. }
  assert (start_id ≤ current_id)%nat as HSIdLeCId by lia.
  clear HEqX.
  iLöb as "IH" forall (current_id γs' v HSIdLeCId) "HSeg HCancelled".
  iAssert (segment_in_list γ γs' current_id v) with "HSeg" as "HSegCopy".
  iDestruct "HSegCopy" as "(Hγs' & HId & HNode)".

  (* Query the ID of the current segment *)
  wp_bind (getId _ _).
  iApply (getId_spec with "HNode").
  iIntros (current_id') "!> #HId'".
  iDestruct (has_value_agrees with "HId HId'") as %<-. iClear "HId'".
  wp_pures.
  wp_bind (if: #(bool_decide _) then _ else _)%E.

  iApply (wp_strong_mono NotStuck _ ⊤ _ _
                         (fun v => ⌜v = #true ∧ (id ≤ current_id)%nat⌝
                                   ∨ ⌜v = #false⌝ ∧
                                     (⌜(current_id < id)%nat⌝ ∨
                                      ⌜(id ≤ current_id)%nat⌝ ∧
                                      segment_is_cancelled γ current_id))%I);
    [done|done| |].
  {
    rewrite bool_decide_decide.
    destruct (decide _) as [HLe|HGt]; wp_pures.
    - wp_apply (getIsRemoved_spec false); first by iFrame "HList HSeg".
      iIntros (r).
      destruct r; [iIntros "#HIsCancelled"|iIntros "_"]; wp_pures.
      + iRight. iSplitR; first done.
        iRight. iSplitR; first by iPureIntro; lia. done.
      + iLeft. iPureIntro. split; first done. lia.
    - iRight. iSplit; first done.
      iLeft. iPureIntro. lia.
  }

  iIntros (?) "[[-> HIdCur]|[-> #HExitReason]]".
  {
    iClear "IH". iModIntro. wp_pures.
    iDestruct "HIdCur" as %HIdCur.
    iApply "HΦ".
    iSplitR. by iExists _.
    iSplit; first by iPureIntro; lia. iAssumption.
  }

  iAssert (∀ newId, (∀ i, ⌜current_id < i < newId⌝ -∗ segment_is_cancelled γ i)
                    -∗ ∀ i, ⌜start_id `max` id ≤ i < newId⌝
                            -∗ segment_is_cancelled γ i)%I
    with "[]" as "HNewCancelled".
  {
    iClear "IH".
    iIntros (?) "HTravCanc".
    iDestruct "HExitReason" as "[HCIdLtId|[HIdLeCId HCurCancelled]]".
    - iDestruct "HCIdLtId" as %HCIdLtId.
      rewrite Max.max_r; last by lia.
      iIntros (? ?). iApply ("HTravCanc" with "[%]"). lia.
    - iDestruct "HIdLeCId" as %HIdLeCId.
      iIntros (k ?).
      destruct (lt_eq_lt_dec k current_id) as [[HLt|HEq]|HGe].
      * iApply "HCancelled". iPureIntro. lia.
      * subst; by iApply "HCurCancelled".
      * iApply "HTravCanc". iPureIntro. lia.
  }
  iClear "HExitReason".

  iModIntro. wp_pures. wp_bind (!_)%E.
  iApply (getNext_spec false with "[]"); first by iFrame "HList HSeg".
  iIntros (r) "!> [[-> _]|HNext]".
  2: {
    iDestruct "HNext" as (nid nptr [-> HC]) "(#HNInList & #HTravCanc)".
    wp_pures.
    iDestruct "HNInList" as (?) "HNInList".
    iApply ("IH" with "[%] HΦ HNInList"); first lia.
    iModIntro.
    iApply "HNewCancelled". iApply "HTravCanc".
  }
  wp_pures.

  wp_bind (getId _ _).
  iApply (getId_spec with "HNode").
  iIntros (current_id') "!> #HId'".
  iDestruct (has_value_agrees with "HId HId'") as %<-. iClear "HId'".
  wp_pures.

  wp_bind (newSegment _ _ _ _). rewrite -Nat2Z.inj_add.
  iApply (list_newSegment_spec with "[]");
    first by iFrame "HInitReq"; iLeft; iExists _; by iSplit.
  iIntros (nγs nv) "!> (HNextSeg & HNextId & HNextNode)".

  wp_pures. wp_bind (trySetNext _ _ _).
  iApply (trySetNext_spec with "[HNextSeg HNextId HNextNode]").
  by iFrame "HList HNextSeg HNextId HNextNode HSeg".
  iIntros (r) "!> HCasResult".
  destruct r; wp_pures; last by iApply ("IH" with "[% //] HΦ HSeg HCancelled").

  iDestruct "HCasResult" as "#HNSeg".

  wp_bind (if: _ then _ else _)%E.
  iApply (wp_strong_mono NotStuck _ ⊤ _ _ (fun v => True)%I); [done|done| |].
  2: {
    iIntros (?) "_ !>". wp_pures.
    iApply ("IH" with "[%] HΦ HNSeg []"); first lia.
    iModIntro. iApply "HNewCancelled". iIntros (? ?); lia.
  }

  wp_bind (getIsRemoved _ _).
  iApply (getIsRemoved_spec false with "[]"); first by iFrame "HList HSeg".
  iIntros (isRemoved) "!> HIsRemoved".
  destruct (isRemoved); wp_pures; last done.
  iApply (remove_spec with "[$]"). done.
Qed.

Definition pointer_location γ ℓ id: iProp :=
  ∃ p γs, ℓ ↦ p ∗ segment_in_list γ γs id p ∗ segment_is_pointed_to γ id.

Lemma tryIncPointersHelper_spec (ℓ: loc):
  ⊢ <<< ∀ pointers slots, ▷ ℓ ↦ #(cleanedAndPointers_contents pointers slots) >>>
    tryIncPointersHelper segment_interface #ℓ @ ⊤
  <<< ∃ (r: bool), if r
      then ⌜pointers ≠ 0 ∨ slots ≠ 0⌝ ∧
           ℓ ↦ #(cleanedAndPointers_contents (S pointers) slots)
      else ⌜pointers = 0 ∧ slots = 0⌝ ∧
           ℓ ↦ #(cleanedAndPointers_contents pointers slots),
      RET #r >>>.
Proof.
  iIntros (Φ) "AU". wp_lam. wp_pures.
  awp_apply (
      addConditionally_spec
        (fun v => negb (Z.eqb v (Z.of_nat (cleanedAndPointers_contents 0 0))))).
  { iIntros (k Φ') "!> _ HΦ'". wp_pures.
    rewrite cleanedAndPointers_contents_zero.
    destruct (decide (k = maxSlots segment_interface)) as [->|HNeq].
    - rewrite Z.eqb_refl bool_decide_true //. by iApply "HΦ'".
    - rewrite bool_decide_false.
      * replace (k =? _)%Z with false; first by iApply "HΦ'".
        symmetry. apply Z.eqb_neq. lia.
      * case. lia.
  }
  iApply (aacc_aupd_commit with "AU"); first done.
  iIntros (pointers slots) "Hℓ". iAaccIntro with "Hℓ"; first by iIntros "$ !> $".
  iIntros "Hℓ !>".
  iExists _. iSplitL; last by iIntros "$".
  destruct (decide (pointers = 0 ∧ slots = 0)) as [[-> ->]|HNeq].
  - rewrite Z.eqb_refl /=. by iFrame.
  - rewrite cleanedAndPointers_contents_zero.
    replace (Z.eqb _ _) with false.
    2: {
      symmetry. apply Z.eqb_neq. intros H'.
      apply Z_of_nat_inj in H'. move: H'.
      apply cleanedAndPointers_contents_nonzero.
      lia.
    }
    simpl. iSplitR; first by iPureIntro; lia.
    rewrite /cleanedAndPointers_contents /=.
    rewrite Z.shiftl_mul_pow2; last by lia.
    replace 2%Z with (Z.of_nat 2) by lia.
    rewrite -Z2Nat_inj_pow Z.mul_1_l -Nat2Z.inj_add.
    rewrite -Nat.add_assoc Nat.add_comm -Nat.add_assoc.
    rewrite Nat.add_comm.
    iFrame.
Qed.

Lemma decPointers_spec γ γs p id:
  {{{ inv N (concurrentLinkedList_invariant γ) ∗ segment_in_list γ γs id p ∗
      segment_is_pointed_to γ id }}}
    decPointers segment_interface p
  {{{ (r: bool), RET #r; if r then segment_is_cancelled γ id else True }}}.
Proof.
  iIntros (Φ) "(#HList & #HSeg & HPtr) HΦ". wp_lam. wp_pures.

  wp_bind (getCleanedAndPointersLoc _ _).
  iDestruct "HSeg" as "(Hγs & HId & HNode)".
  iApply (getCleanedAndPointersLoc_spec with "HNode").
  iIntros (cℓ) "!> #HValcℓ".

  wp_bind (addAndGet _ _).
  awp_apply addAndGet_spec without "HΦ". iInv "HList" as "HOpen".
  iDestruct (concurrentLinkedList_insert with "Hγs HOpen")
    as (list pointers slots) "(>HLookup & HSeg & >Hγ & HRestore)".
  iDestruct "HLookup" as %HLookup.
  iDestruct "HSeg" as "([HContents HSlot] & HNode' & HId' & Hcℓ & HRest)".
  iDestruct "Hcℓ" as (cℓ') "[#HValcℓ' Hcℓ]".
  iDestruct (has_value_agrees with "HValcℓ HValcℓ'") as "><-".
  iAaccIntro with "Hcℓ".
  { iIntros "Hcℓ". iFrame "HPtr". iModIntro. iApply "HRestore".
    iExists _, _. rewrite list_insert_id //. iFrame "Hγ".
    iFrame "HContents HSlot HNode' HId' HRest". iExists cℓ.
    iFrame "Hcℓ HValcℓ". }
  iIntros "Hcℓ".
  destruct pointers as [|pointers'].
  { (* Impossible: we have evidence of at least one pointer existing. *)
    destruct slots.
    * iDestruct (own_valid_2 with "Hγ HPtr") as
          %[(? & HLookup' & HInc)%list_singletonM_included _]%auth_both_valid.
      rewrite map_lookup HLookup /= in HLookup'. simplify_eq.
      apply prod_included in HInc. destruct HInc as [_ HInc].
      apply Some_included in HInc. exfalso.
      simpl in *.
      destruct HInc as [HContra|HContra].
      - inversion HContra.
      - apply csum_included in HContra.
        by destruct HContra as [?|[(? & ? & ? & ?)|(? & ? & ? & ? & ?)]].
    * iDestruct "HSlot" as ">HSlot".
      iCombine "HSlot" "HPtr" as "HFrag".
      iDestruct (own_valid_2 with "Hγ HFrag") as %[HValid _]%auth_both_valid.
      exfalso. move: HValid.
      rewrite list_singletonM_op list_singletonM_included map_lookup HLookup /=.
      intros (? & HLookup' & HInc); simplify_eq.
      apply prod_included in HInc. destruct HInc as [_ HInc].
      apply Some_included in HInc.
      simpl in *.
      destruct HInc as [HContra|HContra].
      - inversion HContra; simplify_eq.
      - apply csum_included in HContra.
        rewrite -Cinr_op in HContra.
        destruct HContra as [?|[(? & ? & ? & ?)|(? & ? & ? & ? & HInc)]].
        + done.
        + done.
        + simplify_eq. apply pos_included in HInc. move: HInc. by compute.
  }
  replace (_ + _)%Z with
      (Z.of_nat (cleanedAndPointers_contents pointers' slots)).
  2: {
    rewrite /cleanedAndPointers_contents.
    rewrite Z.shiftl_mul_pow2; last lia.
    replace 2%Z with (Z.of_nat 2) by lia.
    rewrite -Z2Nat_inj_pow Z.mul_1_l.
    rewrite Z.add_opp_r -Nat2Z.inj_sub; last lia.
    congr Z.of_nat. lia.
  }

  iAssert (▷ is_segment γ (length list =? S id) id γs pointers' slots)%I
    with "[-HRestore HPtr Hγ]" as "HSeg".
  {
    iFrame "HContents HSlot HNode' HId' HRest".
    iExists cℓ. by iFrame.
  }
  destruct (decide (pointers' = 0 ∧ slots = 0)) as [[-> ->]|HNeq].
  - iAssert (|==> own γ (auth_ra (<[id := (γs, (0, 0))]> list))
                  ∗ segment_is_cancelled γ id)%I
      with "[Hγ HPtr]" as ">[Hγ HIsCancelled]".
    {
      iMod (own_update_2 with "Hγ HPtr") as "[$ $]"; last done.
      apply auth_update. apply list_lookup_local_update. intros i.
      rewrite list_fmap_insert map_lookup.
      destruct (lt_eq_lt_dec i id) as [[HLt| ->]|HGt].
      - rewrite list_lookup_insert_ne; last lia.
        rewrite !list_lookup_singletonM_lt; try lia.
        by rewrite map_lookup.
      - rewrite !list_lookup_singletonM.
        rewrite list_lookup_insert;
          last by rewrite fmap_length; eapply lookup_lt_Some.
        rewrite HLookup /=.
        apply option_local_update, prod_local_update_2. simpl.
        replace (Pos.of_nat 1) with 1%positive by (compute; done).
        apply option_local_update, replace_local_update; try done.
        apply _.
      - rewrite list_lookup_insert_ne; last lia.
        rewrite !list_lookup_singletonM_gt; try lia.
        by rewrite map_lookup.
    }
    iSplitR "HIsCancelled"; iModIntro.
    * iApply "HRestore". iExists _, _; iFrame.
    * iIntros "HΦ". wp_pures.
      rewrite cleanedAndPointers_contents_zero.
      iApply "HΦ".
      rewrite bool_decide_true //.
  - iAssert (|==> own γ (auth_ra (<[id := (γs, (pointers', slots))]> list))
            ∗ own γ (◯ {[ id := ε ]}))%I
      with "[Hγ HPtr]" as ">[Hγ _]".
    {
      iMod (own_update_2 with "Hγ HPtr") as "[$ $]"; last done.
      apply auth_update. apply list_lookup_local_update. intros i.
      rewrite list_fmap_insert map_lookup.
      destruct (lt_eq_lt_dec i id) as [[HLt| ->]|HGt].
      - rewrite list_lookup_insert_ne; last lia.
        rewrite !list_lookup_singletonM_lt; try lia.
        by rewrite map_lookup.
      - rewrite !list_lookup_singletonM.
        rewrite list_lookup_insert;
          last by rewrite fmap_length; eapply lookup_lt_Some.
        rewrite HLookup /=.
        apply option_local_update, prod_local_update_2. simpl.
        rewrite decide_False; last lia.
        remember (_ + _) as k.
        destruct k as [|k']; first by destruct slots; lia.
        rewrite -!Pos.of_nat_succ /=.
        replace (Pos.succ (Pos.of_succ_nat k'))
          with (1%positive ⋅ Pos.of_succ_nat k')
          by rewrite pos_op_plus Pplus_one_succ_l //.
        rewrite Cinr_op Some_op /=.
        by apply (cancel_local_update_unit (Some (Cinr 1%positive))), _.
      - rewrite list_lookup_insert_ne; last lia.
        rewrite !list_lookup_singletonM_gt; try lia.
        by rewrite map_lookup.
    }
    iSplitR ""; iModIntro.
    * iApply "HRestore". iExists _, _; iFrame.
    * iIntros "HΦ". wp_pures.
      iApply "HΦ".
      rewrite bool_decide_false //.
      case. intros HContra. apply Nat2Z.inj in HContra.
      move: HContra. apply cleanedAndPointers_contents_nonzero. lia.
Qed.

Theorem moveForward_spec γ γs (ℓ: loc) id p:
  is_concurrentLinkedList γ -∗
  segment_in_list γ γs id p -∗
  <<< ∀ id', ▷ pointer_location γ ℓ id' >>>
    moveForward segment_interface #ℓ p @ ⊤ ∖ ↑N
  <<< ∃ (r: bool), if r
                   then pointer_location γ ℓ (max id id')
                   else ▷ pointer_location γ ℓ id' ∗ segment_is_cancelled γ id,
      RET #r >>>.
Proof.
  iIntros "#[HList _] #HSeg" (Φ) "AU". wp_lam. wp_pures. wp_pures. iLöb as "IH".
  wp_bind (!_)%E. iMod "AU" as (id') "[Hp HClose]".
  iDestruct "Hp" as (p' ?) "(Hℓ & #HSeg' & HPtr')".
  wp_load.
  iDestruct "HSeg" as "(#Hγs & #HId & #HNode)".
  iDestruct "HSeg'" as  "(#Hγs' & #HId' & #HNode')".
  destruct (decide (id ≤ id')) as [HIdLeId'|HIdGtId'].
  { iDestruct "HClose" as "[_ HClose]".
    iMod ("HClose" $! true with "[-]") as "HΦ".
    { rewrite Nat.max_r; last lia. iExists p'; iFrame.
      iExists _. iFrame "Hγs' HId' HNode'". }
    iModIntro. wp_pures.

    wp_bind (getId _ _). iApply (getId_spec with "HNode'").
    iIntros (id'2) "!> HId'2".
    iDestruct (has_value_agrees with "HId' HId'2") as %<-.

    wp_bind (getId _ _). iApply (getId_spec with "HNode").
    iIntros (id2) "!> HId2".
    iDestruct (has_value_agrees with "HId HId2") as %<-.

    wp_pures. rewrite bool_decide_true; last lia. by wp_pures.
  }
  iDestruct "HClose" as "[HClose _]".
  iMod ("HClose" with "[-]") as "AU".
  { iExists _. iFrame. iExists _. iFrame "Hγs' HId' HNode'". }

  iModIntro. wp_pures.

  wp_bind (getId _ _). iApply (getId_spec with "HNode'").
  iIntros (id'2) "!> HId'2".
  iDestruct (has_value_agrees with "HId' HId'2") as %<-.

  wp_bind (getId _ _). iApply (getId_spec with "HNode").
  iIntros (id2) "!> HId2".
  iDestruct (has_value_agrees with "HId HId2") as %<-.

  wp_pures. rewrite bool_decide_false; last lia. wp_pures. wp_lam.
  iClear "HId'2 HId2".

  wp_bind (getCleanedAndPointersLoc _ _).
  iApply (getCleanedAndPointersLoc_spec with "HNode").
  iIntros (cℓ) "!> #HValcℓ".

  wp_bind (tryIncPointersHelper _ _).
  awp_apply tryIncPointersHelper_spec.
  iInv "HList" as "HOpen".
  iApply (aacc_aupd with "AU"); first done.
  (* This value doesn't mean anything; we only need to open this AU to be able to
     exit early if tryIncPointersHelper fails. *)
  iIntros (?) "HPointer".
  iDestruct (concurrentLinkedList_insert with "Hγs HOpen")
            as (list pointers slots) "(>HLookup & HSeg & >Hγ & HRestore)".
  iDestruct "HLookup" as %HLookup.
  iDestruct "HSeg" as "(HSegContent & HNode2 & HId3 & Hcℓ & HRest)".
  iDestruct "Hcℓ" as (cℓ') "[>HValcℓ2 Hcℓ']".
  iDestruct (has_value_agrees with "HValcℓ HValcℓ2") as %<-.
  iAaccIntro with "Hcℓ'".
  {
    iIntros "Hcℓ". iFrame "HPointer". iIntros "!> $". iModIntro.
    iApply "HRestore". iExists _, _. rewrite list_insert_id; last done.
    iFrame "Hγ". iFrame "HSegContent HNode2 HId3 HRest".
    iExists cℓ. iFrame.
  }
  iIntros (r) "Hr". destruct r.
  2: {
    iRight. iDestruct "Hr" as ([-> ->]) "Hcℓ". iExists false. iFrame "HPointer".
    iMod (own_update with "Hγ") as "[Hγ $]".
    { apply auth_update_core_id; first by apply _.
      apply list_singletonM_included. eexists.
      rewrite list_lookup_fmap HLookup /=.
      split; first done.
      apply pair_included. split; first by apply ucmra_unit_least.
      done.
    }
    iIntros "!> HΦ".
    iModIntro. iSplitR "HΦ".
    {
      iApply "HRestore". iExists _, _. rewrite list_insert_id; last done.
      iFrame "Hγ". iFrame "HSegContent HNode2 HId3 HRest".
      iExists cℓ. iFrame.
    }
    by wp_pures.
  }
  iLeft. iFrame "HPointer". iIntros "!> AU".
  iDestruct "Hr" as (?) "Hcℓ".
  iAssert (|==> own γ (auth_ra (<[id := (γs, (S pointers, slots))]> list)) ∗
                segment_is_pointed_to γ id)%I
          with "[Hγ]" as ">[Hγ HSegmentPtr]".
  {
    iMod (own_update with "Hγ") as "[$ $]"; last done.
    apply auth_update_alloc.
    rewrite list_fmap_insert.
    apply list_lookup_local_update. intros i.
    rewrite lookup_nil map_lookup.
    destruct (lt_eq_lt_dec i id) as [[HLt| ->]|HLt].
    - rewrite list_lookup_singletonM_lt; last done.
      rewrite list_lookup_insert_ne; last lia.
      rewrite map_lookup.
      assert (is_Some (list !! i)) as [? ->].
      { apply lookup_lt_is_Some. apply lookup_lt_Some in HLookup. lia. }
      simpl.
      apply option_local_update'''.
      by rewrite ucmra_unit_left_id.
      intros ?. by rewrite ucmra_unit_left_id.
    - rewrite HLookup list_lookup_singletonM list_lookup_insert /=.
      2: by rewrite fmap_length; eapply lookup_lt_Some.
      simpl.
      apply option_local_update'''.
      * rewrite -pair_op ucmra_unit_left_id -Some_op.
        rewrite decide_False; last lia.
        rewrite -Cinr_op pos_op_plus.
        replace 1%positive with (Pos.of_nat 1) by (compute; done).
        rewrite -Nat2Pos.inj_add; try done.
        destruct slots; lia.
      * intros. apply cmra_valid_validN.
        rewrite -pair_op. apply pair_valid. split; first done.
        apply Some_valid.
        rewrite decide_False; last lia.
        done.
    - rewrite list_lookup_singletonM_gt; last done.
      rewrite list_lookup_insert_ne; last lia.
      by rewrite map_lookup.
  }
  iSplitR "AU HSegmentPtr".
  {
    iModIntro. iModIntro. iApply "HRestore". iExists _, _. iFrame "Hγ".
    iFrame "HSegContent HNode2 HId3 HRest".
    iExists cℓ; iFrame.
  }
  iModIntro.

  wp_pures. wp_bind (CmpXchg _ _ _).
  iMod "AU" as (id'') "[Hp'' HClose]".
  iDestruct "Hp''" as (p'' ?) "(Hℓ & #HSeg'' & >HPtr'')".
  iDestruct "HSeg''" as "(#Hγs'' & #HId'' & #HNode'')".
  iDestruct (linkedListNode_unboxed with "HNode''") as ">Hp''Unboxed".
  iDestruct "Hp''Unboxed" as %Hp''Unboxed.
  iDestruct (linkedListNode_unboxed with "HNode'") as %Hp'Unboxed.
  destruct (decide (p' = p'')) as [->|HNeq].
  - wp_cmpxchg_suc.
    iDestruct (node_induces_id with "HId' HId'' HNode' HNode''") as ">->".
    iDestruct "HClose" as "[_ HClose]".
    iMod ("HClose" $! true with "[-HPtr'']") as "HΦ".
    {
      rewrite Nat.max_l; last lia.
      iExists _. iFrame. iExists _. iFrame "Hγs HId HNode".
    }

    iModIntro. wp_pures. wp_bind (decPointers _ _).
    iApply (decPointers_spec with "[HPtr'']").
    by iFrame "HList HPtr'' Hγs'' HId'' HNode''".
    iIntros (r) "!> Hr". destruct r; wp_pures; last done.
    wp_bind (remove _ _). iApply (remove_spec with "[Hr]").
    by iFrame "HList Hr Hγs'' HId'' HNode''".
    iIntros "!> _". wp_pures. done.
  - wp_cmpxchg_fail. iDestruct "HClose" as "[HClose _]".
    iMod ("HClose" with "[-HSegmentPtr]") as "AU".
    { iExists _. iFrame. iExists _. iFrame "Hγs'' HId'' HNode''". }
    iModIntro. wp_pures.
    wp_bind (decPointers _ _).
    iApply (decPointers_spec with "[HSegmentPtr]").
    by iFrame "HList HSegmentPtr Hγs HId HNode".
    iIntros (r) "!> Hr". destruct r; wp_pures; last by iApply "IH".
    wp_bind (remove _ _). iApply (remove_spec with "[Hr]").
    by iFrame "HList Hr Hγs HId HNode".
    iIntros "!> _". wp_pures.
    by iApply "IH".
Qed.

Lemma cancelCell_spec Ψ γ γs id p (k: nat):
  inv N (concurrentLinkedList_invariant γ) -∗
  segment_in_list γ γs id p -∗
  <<< (∀ n, segment_content _ _ segment_spec γs n ==∗
       Ψ ∗ ∃ n', ⌜(n = S k + n')%nat⌝ ∧
                 segment_content _ _ segment_spec γs n') >>>
    FAA (getCleanedAndPointersLoc segment_interface p) #(S k) @ ⊤ ∖ ↑N
  <<< ∃ (v: nat), Ψ ∗ if decide (v + S k = maxSlots segment_interface)%nat
                      then segment_is_cancelled γ id
                      else True, RET #v >>>.
Proof.
  iIntros "#HList #(Hγs & HId & HNode)" (Φ) "AU".
  wp_bind (getCleanedAndPointersLoc _ _).
  iApply (getCleanedAndPointersLoc_spec with "HNode").
  iIntros (cℓ) "!> HValcℓ".
  iInv "HList" as "HOpen" "HClose".
  iMod "AU" as "[HUpdater [_ HCloseUpdater]]".
  iDestruct (concurrentLinkedList_insert with "Hγs HOpen")
    as (list pointers slots) "(>HLookup & HSeg & Hγ & HRestore)".
  iDestruct "HLookup" as %HLookup.
  iDestruct "HSeg" as "([HContent HSlots] & HNode' & HId' & Hcℓ & Hpℓ & Hnℓ &
    >HRest)".
  iDestruct "HRest" as %HBound.
  iDestruct "Hcℓ" as (cℓ') "(>HValcℓ' & Hcℓ)".
  iDestruct (has_value_agrees with "HValcℓ HValcℓ'") as %<-.
  wp_faa.
  iMod ("HUpdater" with "HContent") as "[HΨ Hn']".
  iDestruct "Hn'" as (n' ->) "HContent".

  iAssert ((match n' with 0 => True | S _ => segment_has_slots γ id end) -∗
           is_segment γ (length list =? S id) id γs pointers n')%I
           with "[-HCloseUpdater HClose HSlots Hγ HRestore HΨ]" as "HSeg".
  {
    replace (_ + S k)%Z with (Z.of_nat (cleanedAndPointers_contents pointers n'))
      by (rewrite /cleanedAndPointers_contents; lia).
    iIntros "HSlots". iFrame. iSplitL.
    - iExists _. iFrame.
    - iPureIntro. lia.
  }
  simpl.
  destruct (decide (pointers = 0 ∧ n' = 0)%nat) as [[-> ->]|HNotEq].
  - iAssert (|==> own γ (auth_ra (<[id := (γs, (0, 0))]> list)) ∗
                  segment_is_cancelled γ id)%I with "[Hγ HSlots]"
      as ">[Hγ HIsCancelled]".
    {
      iMod (own_update_2 with "Hγ HSlots") as "[$ $]"; last done.
      apply auth_update. apply list_lookup_local_update. intros i.
      rewrite list_fmap_insert.
      destruct (lt_eq_lt_dec i id) as [[HLt| ->]|HGt].
      - rewrite !list_lookup_singletonM_lt; try lia.
        by rewrite list_lookup_insert_ne; last lia.
      - rewrite !list_lookup_singletonM list_lookup_insert;
          last by rewrite fmap_length; eapply lookup_lt_Some.
        rewrite map_lookup HLookup /segment_algebra_from_state /=.
        replace (Pos.of_nat 1) with 1%positive by (compute; done).
        apply option_local_update, prod_local_update_2, option_local_update.
        apply replace_local_update; try done. apply _.
      - rewrite !list_lookup_singletonM_gt; try lia.
        by rewrite list_lookup_insert_ne; last lia.
    }
    iMod ("HCloseUpdater" $! (cleanedAndPointers_contents 0 (S k)) with
         "[HΨ HIsCancelled]") as "HΦ".
    {
      iFrame "HΨ". rewrite decide_True //.
      rewrite /cleanedAndPointers_contents; lia.
    }
    iModIntro.
    iMod ("HClose" with "[HRestore HSeg Hγ]") as "_".
    {
      iApply "HRestore". iExists _, _. iFrame "Hγ".
      by iApply "HSeg".
    }
    iModIntro. by rewrite Nat.add_0_r.
  - iMod ("HCloseUpdater" $! (cleanedAndPointers_contents pointers (S (k + n')))
         with "[HΨ]") as "HΦ".
    {
      iFrame. rewrite decide_False //.
      replace (_ + S k) with (cleanedAndPointers_contents pointers n')
        by (rewrite /cleanedAndPointers_contents; lia).
      apply cleanedAndPointers_contents_nonzero. lia.
    }
    iModIntro.
    destruct n' as [|n''].
    * iAssert (|==> own γ (auth_ra (<[id := (γs, (pointers, 0))]> list)) ∗
                    own γ (◯ ({[ id := ε ]})))%I
        with "[Hγ HSlots]" as ">[Hγ _]".
      {
        iMod (own_update_2 with "Hγ HSlots") as "[$ $]"; last done.
        apply auth_update. apply list_lookup_local_update. intros i.
        rewrite list_fmap_insert.
        destruct (lt_eq_lt_dec i id) as [[HLt| ->]|HGt].
        - rewrite !list_lookup_singletonM_lt; try lia.
          by rewrite list_lookup_insert_ne; last lia.
        - rewrite !list_lookup_singletonM list_lookup_insert;
            last by rewrite fmap_length; eapply lookup_lt_Some.
          rewrite map_lookup HLookup /segment_algebra_from_state /=.
          apply option_local_update, prod_local_update_2.
          destruct pointers; try lia. simpl.
          rewrite Nat.add_1_r Nat.add_0_r.
          rewrite -!Pos.of_nat_succ /=.
          replace (Pos.succ (Pos.of_succ_nat pointers))
            with (1%positive ⋅ Pos.of_succ_nat pointers)
            by rewrite pos_op_plus Pplus_one_succ_l //.
          rewrite Cinr_op Some_op /=.
          by apply (cancel_local_update_unit (Some (Cinr 1%positive))), _.
        - rewrite !list_lookup_singletonM_gt; try lia.
          by rewrite list_lookup_insert_ne; last lia.
      }
      iMod ("HClose" with "[HRestore HSeg Hγ]") as "_".
      {
        iApply "HRestore". iExists _, _. iFrame "Hγ".
        by iApply "HSeg".
      }
      done.
    * replace (auth_ra list) with
          (auth_ra (<[id := (γs, (pointers, S n''))]> list)).
      2: {
        rewrite /auth_ra. congr auth_auth. rewrite list_fmap_insert.
        apply list_eq. intros i.
        destruct (lt_eq_lt_dec i id) as [[HLt| ->]|HGt];
          try (by rewrite list_lookup_insert_ne; try lia).
        rewrite list_lookup_insert;
          last by rewrite fmap_length; eapply lookup_lt_Some.
        rewrite map_lookup HLookup /= /segment_algebra_from_state /=.
        by destruct pointers; simpl.
      }
      iMod ("HClose" with "[HRestore HSeg Hγ HSlots]") as "_".
      {
        iApply "HRestore". iExists _, _. iFrame "Hγ".
        by iApply "HSeg".
      }
      done.
Qed.

Theorem onSlotCleaned_spec Ψ γ γs id p:
  is_concurrentLinkedList γ -∗
  segment_in_list γ γs id p -∗
  <<< (∀ n, segment_content _ _ segment_spec γs n ==∗
       Ψ ∗ ∃ n', ⌜(n = S n')%nat⌝ ∧
                 segment_content _ _ segment_spec γs n') >>>
    onSlotCleaned segment_interface p @ ⊤ ∖ ↑N
  <<< Ψ, RET #() >>>.
Proof.
  iIntros "#[HList _] #HSeg" (Φ) "AU". wp_lam.
  wp_bind (FAA _ _). replace 1%Z with (Z.of_nat 1) by lia.
  awp_apply (cancelCell_spec with "HList HSeg").
  iApply (aacc_aupd_commit with "AU"); first done.
  iIntros "HUpdater". iAaccIntro with "HUpdater".
  by iIntros "$ !> $".
  iIntros (v) "[$ HCanc] !> HΦ !>".
  wp_pures. rewrite -Nat2Z.inj_add !Nat.add_1_r.
  destruct (decide _) as [->|HNeq].
  - rewrite bool_decide_true; last done.
    wp_pures.
    iApply (remove_spec with "[$]").
    by iIntros "!> _".
  - rewrite bool_decide_false. by wp_pures.
    case. lia.
Qed.

Theorem access_segment (known_is_removed: bool) E γ γs id ptr:
  ↑N ⊆ E ->
  is_concurrentLinkedList γ -∗
  segment_in_list γ γs id ptr -∗
  (if known_is_removed then segment_is_cancelled γ id else True) -∗
  |={E, E ∖ ↑N}=> ∃ n, ⌜known_is_removed = false ∨ n = 0⌝ ∧
                       ▷ segment_content _ _ _ γs n ∗
                       (▷ segment_content _ _ _ γs n ={E ∖ ↑N, E}=∗ emp).
Proof.
  iIntros (HSubset) "[HList _] HSeg HKnownRemoved".
  iInv "HList" as "HOpen" "HClose".
  iDestruct "HSeg" as "(Hγs & _ & _)".
  iDestruct (concurrentLinkedList_lookup_acc_known_removed
               with "Hγs HKnownRemoved HOpen")
    as (is_tail pointers slots) "(>HR & [[HContent HSlots] HRest] & HRestore)".
  iDestruct "HR" as %HR.
  iModIntro. iExists _. iFrame "HContent".
  iSplitR.
  - iPureIntro. destruct HR; auto. lia.
  - iIntros "HContent". iMod ("HClose" with "[-]") as "$"; last done.
    iApply "HRestore". iFrame.
Qed.

Theorem cleanPrev_spec γ γs id ptr:
  {{{ is_concurrentLinkedList γ ∗ segment_in_list γ γs id ptr }}}
    cleanPrev (base segment_interface) ptr
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "[#[HList _] (Hγs & HId & HNode)] HΦ". wp_lam.
  wp_bind (getPrevLoc _ _). iApply (getPrevLoc_spec with "HNode").
  iIntros (pℓ) "!> #HValpℓ".
  iInv "HList" as "HOpen" "HClose".
  iDestruct (concurrentLinkedList_lookup_acc with "Hγs HOpen")
    as (? ? ?) "(HSeg & HRestore)".
  iDestruct "HSeg" as "(HContent & HNode' & HId' & Hcℓ & Hpℓ & HRest)".
  iDestruct "Hpℓ" as (pℓ') "[HValpℓ' Hpℓ]".
  iDestruct (has_value_agrees with "HValpℓ HValpℓ'") as "><-".
  iAssert (▷ pℓ ↦ -)%I with "[Hpℓ]" as (?) "Hpℓ".
  { iDestruct "Hpℓ" as "[Hpℓ|Hpℓ]"; first by iExists _.
    iDestruct "Hpℓ" as (? ?) "(_ & _ & _ & Hpℓ)". by iExists _. }
  wp_store.
  iMod ("HClose" with "[-HΦ]") as "_"; last by iApply "HΦ".
  iApply "HRestore". iFrame. iExists _. iFrame "HValpℓ". by iLeft.
Qed.

Lemma read_pointer_location γ (ℓ: loc):
  ⊢ <<< ∀ id, ▷ pointer_location γ ℓ id >>>
    ! #ℓ @ ⊤
  <<< ∃ γs p, pointer_location γ ℓ id ∗ segment_in_list γ γs id p, RET p >>>.
Proof.
  iIntros (Φ) "AU".
  iMod "AU" as (id) "[HPointer [_ HClose]]".
  iDestruct "HPointer" as (p γs) "(Hℓ & #HSeg & HPointed)".
  wp_load.
  iMod ("HClose" with "[-]") as "HΦ"; last by iFrame.
  iFrame "HSeg". iExists _, _. by iFrame.
Qed.

Theorem newList_spec (k: nat):
  {{{ ⌜k > 0⌝ ∧ initialization_requirements _ _ segment_spec }}}
    (λ: "k", AllocN "k" (newSegment segment_interface #0%nat NONEV "k"))%V #k
  {{{ γ ℓ, RET #ℓ; is_concurrentLinkedList γ ∗
                   [∗ list] i ∈ seq 0 k, pointer_location γ (ℓ +ₗ Z.of_nat i) 0
  }}}.
Proof.
  iIntros (Φ) "[% #HInitReq] HΦ". rewrite -wp_fupd. wp_pures.
  wp_bind (newSegment _ _ _ _). iApply (newSegment_spec with "HInitReq").
  iIntros (γs node pℓ nℓ cℓ) "!> HSeg".
  iDestruct "HSeg" as "(#HIsNode & HContent & #HId & HRest)".
  wp_alloc dℓ as "Hdℓ"; first lia. rewrite /array.
  iMod (own_alloc (auth_ra [(γs, (k, maxSlots segment_interface))] ⋅
                   (◯ {[ 0%nat := (Some (to_agree γs), ε): segment_algebra ]} ⋅
                    ◯ {[ 0%nat := (ε, Some (Cinr (Pos.of_nat (S k)))):
                                    segment_algebra ]})))
    as (γ) "[Hγ [#Hγs HPointer]]".
  {
    rewrite -auth_frag_op list_singletonM_op -pair_op.
    rewrite ucmra_unit_left_id ucmra_unit_right_id.
    rewrite /auth_ra /segment_algebra_from_state /=.
    apply auth_both_valid. split.
    - apply list_singletonM_included.
      eexists. split; first done.
      apply prod_included=> /=. split; first done.
      rewrite decide_False; last lia.
      move: (max_slots_bound _ _ segment_spec)=> ?.
      destruct (maxSlots _); first lia.
      by rewrite Nat.add_1_r.
    - apply list_lookup_valid.
      case=> [|n'] //=.
      rewrite Some_valid /segment_algebra_from_state pair_valid.
      split; first done.
      by destruct (decide _).
  }
  iAssert ([∗] replicate (S k) (segment_is_pointed_to γ 0))%I
    with "[HPointer]" as "HPointedTo".
  {
    clear. iInduction (k) as [|k] "IH"; rewrite //=.
    - rewrite /segment_is_pointed_to.
      replace (Pos.of_nat 1) with 1%positive; first by iFrame.
      by compute.
    - replace (Pos.of_nat (S (S k))) with (1%positive ⋅ Pos.of_nat (S k)).
      * rewrite Cinr_op Some_op pair_op_2 -list_singletonM_op auth_frag_op.
        iDestruct "HPointer" as "[$ HInd]".
        by iApply "IH".
      * rewrite -!Pos.of_nat_succ /= pos_op_plus Pos.add_1_l //.
  }
  simpl.
  iDestruct "HPointedTo" as "[HSlots HPointedTo]".
  iAssert (segment_in_list γ γs 0 node) with "[]" as "#HSeg".
  by iFrame "HIsNode HId Hγs".
  iAssert (is_segment γ true 0 γs k (maxSlots segment_interface))
          with "[HContent HRest HSlots]" as "HIsSeg".
  {
    iFrame "HContent HId".
    iSplitL "HSlots".
    { move: (max_slots_bound _ _ segment_spec)=> ?.
      destruct (maxSlots _); [lia|done]. }
    iSplitR; first by iExists _.
    iDestruct "HRest" as "(#HValcℓ & #HValpℓ & #HValnℓ & Hpℓ & Hnℓ & Hcℓ)".
    iSplitL "Hcℓ"; last iSplitL "Hpℓ"; last iSplitL; last by iPureIntro.
    - iExists cℓ. iFrame "HValcℓ". rewrite /cleanedAndPointers_contents.
      rewrite Nat.sub_diag Nat.add_0_r Z.shiftl_mul_pow2; last lia.
      rewrite Nat2Z.inj_mul Z2Nat_inj_pow.
      iFrame "Hcℓ".
    - iExists pℓ. iFrame "HValpℓ". by iLeft.
    - iExists nℓ. iFrame "HValnℓ". done.
  }
  iMod (inv_alloc N _ (concurrentLinkedList_invariant γ) with "[Hγ HIsSeg]")
    as "#HInv".
  { iExists _. iFrame "Hγ HIsSeg". simpl. done. }
  iApply "HΦ". iFrame "HInv HInitReq". iModIntro.

  rewrite Nat2Z.id. clear.

  assert (∃ n, n = 0) as [n HNeq] by eauto.
  iAssert ([∗ list] i ↦ v ∈ replicate k node, (dℓ +ₗ (n + i)) ↦ v)%I
          with "[Hdℓ]" as "Hdℓ".
  { subst. done. }
  replace (seq 0 k) with (seq n k) by auto.
  clear HNeq.

  iInduction (k) as [|k'] "IH" forall (n); first done.
  simpl.
  iDestruct "Hdℓ" as "[Hdℓ HdℓRest]".
  iDestruct "HPointedTo" as "[HPointedTo HPointedToRest]".
  iSplitL "HPointedTo Hdℓ".
  - iExists _, _. rewrite Z.add_0_r. by iFrame.
  - iApply ("IH" with "HPointedToRest [HdℓRest]").
    iApply (big_sepL_mono with "HdℓRest"). intros. simpl.
    by rewrite -!Nat2Z.inj_add -plus_n_Sm.
Qed.

End concurrentLinkedListProof.

Canonical Structure list_impl `{!heapG Σ}
          {impl: segmentInterface} (segment_spec: segmentSpec Σ impl)
          `{!iLinkedListG segment_spec Σ}: listSpec Σ segment_spec :=
  {|
     list_spec.findSegment_spec := findSegmentInternal_spec segment_spec;
     list_spec.moveForward_spec := moveForward_spec segment_spec;
     list_spec.cleanPrev_spec := cleanPrev_spec segment_spec;
     list_spec.access_segment := access_segment segment_spec;
     list_spec.pointer_location_load := read_pointer_location segment_spec;
     list_spec.onSlotCleaned_spec := onSlotCleaned_spec segment_spec;
     list_spec.newList_spec := newList_spec segment_spec;
  |}.
