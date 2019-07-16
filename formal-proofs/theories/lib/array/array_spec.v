From iris.heap_lang Require Import proofmode notation lang.
From iris.program_logic Require Export atomic.

Record array_spec {Σ} `{!heapG Σ} :=
  AtomicArray {
      make_array : val;
      array_load : val;
      array_store : val;

      name : Type;
      name_eqdec : EqDecision name;
      name_countable : Countable name;

      is_array (N: namespace) (γs: name) (v: val) (n: nat): iProp Σ;
      array_content (γs : name) {n : nat} (l : vec val n) : iProp Σ;

      is_array_persistent N γs v n: Persistent (is_array N γs v n);
      array_content_timeless γs n l: Timeless (@array_content γs n l);
      array_content_exclusive γs n l1 m l2 :
        @array_content γs n l1 -∗ @array_content γs m l2 -∗ False;

      new_array_spec N k v:
        {{{ True }}}
          make_array #k v
        {{{ γs s, RET s;
            is_array N γs s k
                     ∗ array_content γs (VectorDef.const v k) }}};

      array_load_spec N γs a (n i : nat) (p: (i < n)%nat):
        is_array N γs a n -∗
        <<< ∀ (l : vec val n), @array_content γs n l >>>
          array_load a #i @ ⊤∖↑N
        <<< array_content γs l, RET (Vector.nth l (fin_of_nat p)) >>>;

      array_store_spec N γs a (n i : nat) (p: (i < n)%nat) (v : val):
        is_array N γs a n -∗
        <<< ∀ (l : vec val n), @array_content γs n l >>>
          array_store a #i v @ ⊤∖↑N
        <<< array_content γs (Vector.replace l (fin_of_nat p) v), RET #() >>>
    }.

Existing Instances
         is_array_persistent array_content_timeless name_countable name_eqdec.
