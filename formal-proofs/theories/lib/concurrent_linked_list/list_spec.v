From SegmentQueue.lib.concurrent_linked_list
     Require Export list_interfaces segment_spec.
From iris.program_logic Require Import atomic.
From iris.heap_lang Require Export proofmode notation lang.
Open Scope nat.

Record listSpec Σ `{!heapG Σ}
       (impl: listInterface)
       {seg_impl: segmentInterface}
       (segment_spec: segmentSpec Σ seg_impl) :=
  ListSpec {
      is_concurrentLinkedList:
        namespace ->
        linkedListNode_parameters _ _ (linkedListNode_base _ _ segment_spec) ->
        gname -> iProp Σ;
      is_concurrentLinkedList_persistent N p γ:
        Persistent (is_concurrentLinkedList N p γ);
      segment_in_list
        (γ: gname)
        (γs: linkedListNode_name _ _ (linkedListNode_base _ _ segment_spec))
        (id: nat)
        (v: val): iProp Σ;
      segment_in_list_persistent γ γs id v:
        Persistent (segment_in_list γ γs id v);
      segment_in_list_agree γ id γs v γs' v':
        segment_in_list γ γs id v -∗ segment_in_list γ γs' id v' -∗
                        ⌜v = v' ∧ γs = γs'⌝;
      segment_is_cancelled: gname -> nat -> iProp Σ;
      segment_is_cancelled_persistent γ id:
        Persistent (segment_is_cancelled γ id);
      pointer_location: gname -> loc -> nat -> iProp Σ;
      segment_in_list_is_node N p E γ γs id v:
        ↑N ⊆ E →
        is_concurrentLinkedList N p γ -∗
        segment_in_list γ γs id v ={E}=∗
        ▷ is_linkedListNode _ _ (linkedListNode_base _ _ segment_spec) p γs v ∗
        ▷ has_value (id_uniqueValue _ _ segment_spec) γs id;
      segment_implies_preceding_segments N p E γ γs id v:
        ↑N ⊆ E →
        is_concurrentLinkedList N p γ -∗
        segment_in_list γ γs id v ={E}=∗
        ∀ i, ⌜i ≤ id⌝ -∗ ∃ γs' v', segment_in_list γ γs' i v';
      newList_spec N p (k: nat):
        {{{ ⌜k > 0⌝ ∧ initialization_requirements _ _ segment_spec }}}
          newList impl #k
        {{{ γ ℓ, RET #ℓ; is_concurrentLinkedList N p γ ∗
                        [∗ list] i ∈ seq 0 k,
                            pointer_location γ (ℓ +ₗ (i: nat)) 0
        }}};
      findSegment_spec N p γ γs' (start_id id: nat) v:
        {{{ is_concurrentLinkedList N p γ ∗ segment_in_list γ γs' start_id v }}}
          findSegment impl v #id
        {{{ (v': val) (id': nat), RET (SOMEV v');
          (∃ γs, segment_in_list γ γs id' v')
          ∗ ⌜(start_id ≤ id' ∧ id ≤ id')%nat⌝
          ∗ ∀ i, (⌜max start_id id ≤ i < id'⌝)%nat -∗ segment_is_cancelled γ i
        }}};
      moveForward_spec N p γ γs (ℓ: loc) id v:
        is_concurrentLinkedList N p γ -∗
        segment_in_list γ γs id v -∗
        <<< ∀ id', ▷ pointer_location γ ℓ id' >>>
          moveForward impl #ℓ v @ ⊤ ∖ ↑N
        <<< ∃ (r: bool), if r then pointer_location γ ℓ (max id id')
                              else ▷ pointer_location γ ℓ id'
                                   ∗ segment_is_cancelled γ id,
            RET #r >>>;
      cleanPrev_spec N p γ γs id ptr:
        {{{ is_concurrentLinkedList N p γ ∗ segment_in_list γ γs id ptr }}}
          cleanPrev impl ptr
        {{{ RET #(); True }}};
      onSlotCleaned_spec N pars Ψ P γ γs id p:
        is_concurrentLinkedList N pars γ -∗
        segment_in_list γ γs id p -∗
        (P ==∗ ∀ n, segment_content _ _ segment_spec γs n ==∗
         Ψ ∗ ∃ n', ⌜(n = S n')%nat⌝ ∧ segment_content _ _ segment_spec γs n') -∗
        <<< P >>>
          onSlotCleaned impl p @ ⊤ ∖ ↑N
        <<< Ψ, RET #() >>>;
      pointer_location_load γ (ℓ: loc):
        ⊢ <<< ∀ id, ▷ pointer_location γ ℓ id >>>
          ! #ℓ @ ⊤
        <<< ∃ γs p, pointer_location γ ℓ id ∗ segment_in_list γ γs id p,
            RET p >>>;
      access_segment N pars (known_is_removed: bool) E γ γs id ptr:
        ↑N ⊆ E ->
        is_concurrentLinkedList N pars γ -∗
        segment_in_list γ γs id ptr -∗
        (if known_is_removed then segment_is_cancelled γ id else True) -∗
        |={E, E ∖ ↑N}=> ∃ n, ⌜known_is_removed = false ∨ n = 0⌝ ∧
                            ▷ segment_content _ _ _ γs n ∗
                            (▷ segment_content _ _ _ γs n ={E ∖ ↑N, E}=∗ emp);
    }.

Existing Instances is_concurrentLinkedList_persistent
         segment_in_list_persistent
         segment_is_cancelled_persistent.
