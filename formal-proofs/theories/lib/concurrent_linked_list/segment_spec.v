From SegmentQueue.lib.concurrent_linked_list Require Export segment_interfaces.
From iris.heap_lang Require Export proofmode notation lang.

Record uniqueValue {Σ} {name value: Type} :=
  UniqueValue {
      has_value (γ: name) (value: value): iProp Σ;
      has_value_persistent (γ: name) (value: value):
        Persistent (has_value γ value);
      has_value_timeless (γ: name) (value: value):
        Timeless (has_value γ value);
      has_value_agrees γ value1 value2:
        has_value γ value1 -∗ has_value γ value2 -∗ ⌜value1 = value2⌝;
    }.

Existing Instance has_value_persistent.
Existing Instance has_value_timeless.

Record linkedListNodeSpec Σ `{!heapG Σ} (impl: linkedListNodeInterface) :=
  LinkedListNodeSpec {
      linkedListNode_name: Type;
      linkedListNode_name_inhabited: Inhabited linkedListNode_name;
      linkedListNode_parameters: Type;
      is_linkedListNode (p: linkedListNode_parameters) (γ: linkedListNode_name)
                        (node: val): iProp Σ;
      prev_uniqueValue: @uniqueValue Σ linkedListNode_name loc;
      next_uniqueValue: @uniqueValue Σ linkedListNode_name loc;
      is_linkedListNode_persistent p γ node:
        Persistent (is_linkedListNode p γ node);
      getPrevLoc_spec p γ node:
        {{{ is_linkedListNode p γ node }}}
          getPrevLoc impl node
        {{{ pℓ, RET #pℓ; has_value prev_uniqueValue γ pℓ }}};
      getNextLoc_spec p γ node:
        {{{ is_linkedListNode p γ node }}}
          getNextLoc impl node
        {{{ nℓ, RET #nℓ; has_value next_uniqueValue γ nℓ }}};
      linkedListNode_unboxed p γ node:
        is_linkedListNode p γ node -∗ ⌜val_is_unboxed node⌝;
    }.

Existing Instance linkedListNode_name_inhabited.
Existing Instance is_linkedListNode_persistent.

Record segmentSpec Σ `{!heapG Σ} (impl: segmentInterface) :=
  SegmentSpec {
      linkedListNode_base: @linkedListNodeSpec Σ _ (base impl);
      id_uniqueValue: @uniqueValue
                        Σ (linkedListNode_name _ _ linkedListNode_base) nat;
      cleanedAndPointers_uniqueValue: @uniqueValue
                        Σ (linkedListNode_name _ _ linkedListNode_base) loc;
      max_slots_bound: (0 < maxSlots impl < 2 ^ pointerShift impl)%nat;
      segment_content: linkedListNode_name _ _ linkedListNode_base →
                       ∀ (alive_slots: nat), iProp Σ;
      initialization_requirements: iProp Σ;
      initialization_requirements_Persistent:
        Persistent initialization_requirements;
      node_induces_id p γ γ' node id id':
        has_value id_uniqueValue γ id -∗
        has_value id_uniqueValue γ' id' -∗
        is_linkedListNode _ _ _ p γ node -∗
        is_linkedListNode _ _ _ p γ' node ==∗
        ⌜id = id'⌝;
      getId_spec p γ node:
        {{{ is_linkedListNode _ _ _ p γ node }}}
          getId impl node
        {{{ id, RET #id; has_value id_uniqueValue γ id }}};
      getCleanedAndPointersLoc_spec p γ node:
        {{{ is_linkedListNode _ _ _ p γ node }}}
          getCleanedAndPointersLoc impl node
        {{{ cℓ, RET #cℓ; has_value cleanedAndPointers_uniqueValue γ cℓ }}};
      newSegment_spec p (id: nat) (prev: val) (pointers: nat):
        {{{ initialization_requirements }}}
          newSegment impl #id prev #pointers
        {{{ γ node pℓ nℓ cℓ, RET node;
            is_linkedListNode _ _ _ p γ node
            ∗ segment_content γ (maxSlots impl)
            ∗ has_value id_uniqueValue γ id
            ∗ has_value cleanedAndPointers_uniqueValue γ cℓ
            ∗ has_value (prev_uniqueValue _ _ _) γ pℓ
            ∗ has_value (next_uniqueValue _ _ _) γ nℓ
            ∗ pℓ ↦ prev ∗ nℓ ↦ NONEV ∗ cℓ ↦ #(pointers ≪ pointerShift impl)
        }}}
    }.

Existing Instance initialization_requirements_Persistent.
