From iris.base_logic.lib Require Export invariants.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation lang.
From iris.program_logic Require Export atomic.
Require Import SegmentQueue.lib.asym_rendezvous.asym_rendezvous_spec.
Require Import SegmentQueue.lib.asym_rendezvous.asym_rendezvous_impl.

From iris.algebra Require Import cmra agree auth excl.

Definition asym_rendezvous_ra :=authR (prodUR
                                         (prodUR
                                            (optionUR (exclR unitO))
                                            (optionUR (exclR unitO)))
                                         (optionUR (agreeR boolO))).

Class asym_rendezvousG Σ := InterruptiblyG {
  asym_rendezvous_stateG :> inG Σ asym_rendezvous_ra;
}.

Definition asym_rendezvousΣ : gFunctors :=
  #[(*GFunctor (exclR unitO);*) GFunctor asym_rendezvous_ra].

Instance subG_asym_rendezvousΣ {Σ} :
  subG asym_rendezvousΣ Σ -> asym_rendezvousG Σ.
Proof. solve_inG. Qed.

Section asym_rendezvous_proof.

Context `{heapG Σ} `{asym_rendezvousG Σ} (N: namespace).

Definition fetch_permit γ := own γ (◯ ((Excl' (), None), None)).

Definition pass_permit γ := own γ (◯ ((None, Excl' ()), None)).

Definition passed γ := own γ (◯ ((None, None), Some (to_agree false))).

Definition cancelled γ := own γ (◯ ((None, None), Some (to_agree true))).

Global Instance passed_persistent γ: Persistent (passed γ).
Proof.
  apply own_core_persistent.
  apply auth_frag_core_id.
  apply pair_core_id; apply _.
Qed.

Global Instance cancelled_persistent γ: Persistent (cancelled γ).
Proof.
  apply own_core_persistent.
  apply auth_frag_core_id.
  apply pair_core_id; apply _.
Qed.

Global Instance pass_permit_timeless γ: Timeless (pass_permit γ).
Proof. apply _. Qed.

Global Instance fetch_permit_timeless γ: Timeless (fetch_permit γ).
Proof. apply _. Qed.

Theorem pass_permit_exclusive γ: pass_permit γ -∗ pass_permit γ -∗ False.
Proof.
  iIntros "H1 H2". rewrite /pass_permit.
  iDestruct (own_valid_2 with "H1 H2") as %HVal.
  inversion HVal as [HVal' _]; simpl in *.
  inversion HVal' as [_ HVal'']; simpl in *.
  inversion HVal''.
Qed.

Theorem fetch_permit_exclusve γ: fetch_permit γ -∗ fetch_permit γ -∗ False.
Proof.
  iIntros "H1 H2". rewrite /pass_permit.
  iDestruct (own_valid_2 with "H1 H2") as %HVal.
  inversion HVal as [HVal' _]; simpl in *.
  inversion HVal' as [HVal'' _]; simpl in *.
  inversion HVal''.
Qed.

Theorem cancelled_not_passed γ: passed γ -∗ cancelled γ -∗ False.
Proof.
  iIntros "H1 H2". rewrite /pass_permit.
  iDestruct (own_valid_2 with "H1 H2") as %HVal.
  inversion HVal as [_ HVal']; simpl in *.
  assert (true = false). { apply HVal'; repeat econstructor. }
  discriminate.
Qed.

Definition asym_rendezvous_inv P ℓ γ :=
   (* Neither reader no writer came yet. *)
  ((own γ (● ((Excl' (), Excl' ()), None)) ∗ ℓ ↦ NONEV) ∨
   (* The writer came and left the resource, but the reader didn't come. *)
   (own γ (● ((Excl' (), None), Some (to_agree false))) ∗ (∃ v, ℓ ↦ RESUMEDV v ∗
                                                                  P v)) ∨
   (* The reader came and broke the cannel; writer wasn't here. *)
   (own γ (● ((None, Excl' ()), Some (to_agree true))) ∗ ℓ ↦ CANCELLEDV) ∨
   (* Both have come; nothing interesting can happen now. *)
   (∃ f, own γ (● ((None, None), Some f))))%I.

End asym_rendezvous_proof.
