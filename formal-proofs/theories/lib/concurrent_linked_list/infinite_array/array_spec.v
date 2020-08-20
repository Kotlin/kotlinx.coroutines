From iris.program_logic Require Import atomic.
From iris.heap_lang Require Export proofmode notation lang.

Record infiniteArraySpec Σ `{!heapG Σ} :=
  InfiniteArraySpec {
      newInfiniteArray: val;
      cancelCell: val;
      findCell: val;
      derefCellPointer: val;
      cutoffMoveForward: val;
      cutoffGetPointer: val;
      infinite_array_name: Type;
      is_infinite_array (N: namespace) (γ: infinite_array_name)
                        (cell_is_owned: nat → iProp Σ): iProp Σ;
      is_infinite_array_persistent N γ co:
        Persistent (is_infinite_array N γ co);
      infinite_array_mapsto (γ: infinite_array_name) (i: nat) (ℓ: loc): iProp Σ;
      infinite_array_mapsto_persistent γ i ℓ:
        Persistent (infinite_array_mapsto γ i ℓ);
      infinite_array_mapsto_agree γ i ℓ ℓ':
        infinite_array_mapsto γ i ℓ -∗ infinite_array_mapsto γ i ℓ' -∗ ⌜ℓ = ℓ'⌝;
      is_infinite_array_cell_pointer (γ: infinite_array_name) (p: val) (i: nat):
          iProp Σ;
      is_infinite_array_cell_pointer_persistent γ p i:
        Persistent (is_infinite_array_cell_pointer γ p i);
      is_infinite_array_cutoff
        (γ: infinite_array_name) (v: val) (start_index: nat): iProp Σ;
      cell_is_cancelled (γ: infinite_array_name) (i: nat): iProp Σ;
      cell_is_cancelled_persistent γ i: Persistent (cell_is_cancelled γ i);
      cell_cancellation_handle (γ: infinite_array_name) (i: nat): iProp Σ;
      cell_cancellation_handle_exclusive γ i:
        cell_cancellation_handle γ i -∗ cell_cancellation_handle γ i -∗ False;
      cell_cancellation_handle_not_cancelled γ i:
        cell_is_cancelled γ i -∗ cell_cancellation_handle γ i -∗ False;
      acquire_cell N γ cell_is_owned i ℓ:
        is_infinite_array N γ cell_is_owned -∗
        infinite_array_mapsto γ i ℓ -∗
        ∀ Φ, (cell_is_owned i ∨ ℓ ↦ NONEV ∗ cell_cancellation_handle γ i
                                ={⊤∖↑N}=∗ cell_is_owned i ∗ Φ) ==∗ Φ;
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
            then is_infinite_array_cutoff γ v (max start_index i)
            else ▷ is_infinite_array_cutoff γ v start_index ∗
                cell_is_cancelled γ start_index, RET #success >>>;
      cutoffGetPointer_spec γ (v: val):
        ⊢ <<< ∀ start_index, ▷ is_infinite_array_cutoff γ v start_index >>>
          cutoffGetPointer v @ ⊤
        <<< ∃ (p: val), is_infinite_array_cutoff γ v start_index ∗
                        is_infinite_array_cell_pointer γ p start_index, RET p >>>
    }.
