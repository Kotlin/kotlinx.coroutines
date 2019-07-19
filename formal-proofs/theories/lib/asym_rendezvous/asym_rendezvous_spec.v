From iris.heap_lang Require Import proofmode.
From iris.heap_lang Require Import notation lang.
Require Export SegmentQueue.lib.util.interruptibly.

Notation CANCELLED := (SOME NONE) (only parsing).
Notation RESUMED x := (SOME (SOME x)) (only parsing).
Notation CANCELLEDV := (SOMEV NONEV) (only parsing).
Notation RESUMEDV x := (SOMEV (SOMEV x)) (only parsing).

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
    (P : val -> iProp Σ): iProp Σ;
  pass_permit (γ: asym_rendezvous_names) : iProp Σ;
  fetch_permit (γ: asym_rendezvous_names) : iProp Σ;
  passed (γ: asym_rendezvous_names) : iProp Σ;
  cancelled (γ: asym_rendezvous_names) : iProp Σ;
  (* -- general properties -- *)
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
    {{{ sm, RET sm; P sm }}};
  await_interruptibly_spec Ni γi handle N γ r P:
    {{{ is_interrupt_handle Ni γi handle ∗
                            is_asym_rendezvous N γ r P ∗
                            fetch_permit γ }}}
      await_interruptibly handle r
    {{{ sm, RET sm; (∃ v, ⌜sm = (#false, RESUMEDV v)%V⌝ ∧ P v) ∨
                    (∃ v, ⌜sm = (#true, RESUMEDV v)%V⌝ ∧ P v ∧ interrupted γi) ∨
                    (⌜sm = (#true, NONEV)%V⌝ ∧ cancelled γ)
    }}};
  pass_spec N γ r P v:
    {{{ is_asym_rendezvous N γ r P ∗ pass_permit γ ∗ P v }}}
      pass r v
    {{{ sm, RET sm; ⌜sm = NONEV⌝ ∧ passed γ ∨ ⌜sm = CANCELLEDV⌝ ∧ P v }}}
}.

Existing Instances is_asym_rendezvous_persistent.
Existing Instances pass_permit_timeless.
Existing Instances fetch_permit_timeless.
Existing Instances passed_persistent.
Existing Instances cancelled_persistent.
