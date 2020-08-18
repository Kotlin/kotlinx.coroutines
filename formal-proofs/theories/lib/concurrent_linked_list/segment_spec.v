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
      is_linkedListNode (γ: linkedListNode_name) (node: val): iProp Σ;
      prev_uniqueValue: @uniqueValue Σ linkedListNode_name loc;
      next_uniqueValue: @uniqueValue Σ linkedListNode_name loc;
      is_linkedListNode_persistent γ node:
        Persistent (is_linkedListNode γ node);
      getPrevLoc_spec γ node:
        {{{ is_linkedListNode γ node }}}
          getPrevLoc impl node
        {{{ pℓ, RET #pℓ; has_value prev_uniqueValue γ pℓ }}};
      getNextLoc_spec γ node:
        {{{ is_linkedListNode γ node }}}
          getNextLoc impl node
        {{{ nℓ, RET #nℓ; has_value next_uniqueValue γ nℓ }}};
      linkedListNode_unboxed γ node:
        is_linkedListNode γ node -∗ ⌜val_is_unboxed node⌝;
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
                       ∀ (id alive_slots: nat), iProp Σ;
      node_induces_id γ γ' node id id':
        has_value id_uniqueValue γ id -∗
        has_value id_uniqueValue γ' id' -∗
        is_linkedListNode _ _ _ γ node -∗
        is_linkedListNode _ _ _ γ' node ==∗
        ⌜id = id'⌝;
      getId_spec γ node:
        {{{ is_linkedListNode _ _ _ γ node }}}
          getId impl node
        {{{ id, RET #id; has_value id_uniqueValue γ id }}};
      getCleanedAndPointersLoc_spec γ node:
        {{{ is_linkedListNode _ _ _ γ node }}}
          getCleanedAndPointersLoc impl node
        {{{ cℓ, RET #cℓ; has_value cleanedAndPointers_uniqueValue γ cℓ }}};
      newSegment_spec (id: nat) (prev: val) (pointers: nat):
        {{{ True }}}
          newSegment impl #id prev #pointers
        {{{ γ node pℓ nℓ cℓ, RET node;
            is_linkedListNode _ _ _ γ node
            ∗ segment_content γ id (maxSlots impl)
            ∗ has_value id_uniqueValue γ id
            ∗ has_value cleanedAndPointers_uniqueValue γ cℓ
            ∗ has_value (prev_uniqueValue _ _ _) γ pℓ
            ∗ has_value (next_uniqueValue _ _ _) γ nℓ
            ∗ pℓ ↦ prev ∗ nℓ ↦ NONEV ∗ cℓ ↦ #(pointers ≪ pointerShift impl)
        }}}
    }.
