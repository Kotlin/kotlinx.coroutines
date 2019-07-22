From iris.heap_lang Require Import proofmode.
From iris.heap_lang Require Import notation lang.
Require Export SegmentQueue.lib.util.interruptibly.

Notation CANCELLED := (SOME #true) (only parsing).
Notation RESUMED := (SOME #false) (only parsing).
Notation CANCELLEDV := (SOMEV #true) (only parsing).
Notation RESUMEDV := (SOMEV #false) (only parsing).

Record asym_rendezvous {Σ} `{heapG Σ} `{interruptiblyG Σ} := Rendezvous {
  (* -- operations -- *)
  init_exchange : val;
  await : val;
  await_interruptibly : val;
  pass : val;
  (* -- predicates -- *)
  asym_rendezvous_names: Type;
  is_asym_rendezvous
    (N: namespace)
    (γ: asym_rendezvous_names)
    (rendezvous: val)
    (P : iProp Σ): iProp Σ;
  pass_permit (γ: asym_rendezvous_names) : iProp Σ;
  fetch_permit (γ: asym_rendezvous_names) : iProp Σ;
  passed (γ: asym_rendezvous_names) : iProp Σ;
  cancelled (γ: asym_rendezvous_names) : iProp Σ;
  (* -- general properties -- *)
  is_asym_rendezvous_ne N γ r: NonExpansive (is_asym_rendezvous N γ r);
  is_asym_rendezvous_persistent N γ r P: Persistent (is_asym_rendezvous N γ r P);
  pass_permit_timeless γ: Timeless (pass_permit γ);
  fetch_permit_timeless γ: Timeless (fetch_permit γ);
  pass_permit_exclusve γ: pass_permit γ -∗ pass_permit γ -∗ False;
  fetch_permit_exclusve γ: fetch_permit γ -∗ fetch_permit γ -∗ False;
  passed_persistent γ: Persistent (passed γ);
  cancelled_persistent γ: Persistent (cancelled γ);
  cancelled_not_passed γ: passed γ -∗ cancelled γ -∗ False;
  (* -- operation specs -- *)
  init_exchange_spec N ℓ P:
    {{{ ∃ v, ℓ ↦ v }}}
      init_exchange #ℓ
    {{{ γ, RET #(); is_asym_rendezvous N γ #ℓ P }}};
  await_spec N γ r P:
    {{{ is_asym_rendezvous N γ r P ∗ fetch_permit γ }}}
      await r
    {{{ RET #(); P ∗ passed γ }}};
  await_interruptibly_spec Ni γi handle N γ r P:
    {{{ is_interrupt_handle Ni γi handle ∗
                            is_asym_rendezvous N γ r P ∗
                            fetch_permit γ }}}
      await_interruptibly handle r
    {{{ sm, RET sm; ⌜sm = (#false, RESUMEDV)%V⌝ ∧ P ∗ passed γ ∨
                    ⌜sm = (#true, RESUMEDV)%V⌝ ∧ ▷P ∗ passed γ ∗ interrupted γi ∨
                    ⌜sm = (#true, NONEV)%V⌝ ∧ cancelled γ
    }}};
  pass_spec N γ r P:
    Laterable P ->
    {{{ is_asym_rendezvous N γ r P ∗ pass_permit γ ∗ P }}}
      pass r
    {{{ sm, RET sm; ⌜sm = NONEV⌝ ∧ passed γ ∨
                                    ⌜sm = CANCELLEDV⌝ ∧ P ∗ cancelled γ}}}
}.

Existing Instances is_asym_rendezvous_persistent.
Existing Instances pass_permit_timeless.
Existing Instances fetch_permit_timeless.
Existing Instances passed_persistent.
Existing Instances cancelled_persistent.
