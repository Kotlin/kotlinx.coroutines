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
  iDestruct (own_valid_2 with "H1 H2") as %[[_ []] _].
Qed.

Theorem fetch_permit_exclusve γ: fetch_permit γ -∗ fetch_permit γ -∗ False.
Proof.
  iIntros "H1 H2". rewrite /pass_permit.
  iDestruct (own_valid_2 with "H1 H2") as %[[[] _] _].
Qed.

Theorem cancelled_not_passed γ: passed γ -∗ cancelled γ -∗ False.
Proof.
  iIntros "H1 H2". rewrite /pass_permit.
  iDestruct (own_valid_2 with "H1 H2") as %[_ HVal'].
  assert (true = false). { apply HVal'; repeat econstructor. }
  discriminate.
Qed.

Definition asym_rendezvous_inv P ℓ γ :=
   (* Neither reader no writer came yet. *)
  ((own γ (● ((Excl' (), Excl' ()), None)) ∗ ℓ ↦ NONEV) ∨
   (* The writer came and left the resource, but the reader didn't come. *)
   (own γ (● ((Excl' (), None), Some (to_agree false))) ∗
        (∃ v, ℓ ↦ RESUMEDV v ∗ P v)) ∨
   (* The reader came and broke the cannel; writer wasn't here. *)
   (own γ (● ((None, Excl' ()), Some (to_agree true))) ∗ ℓ ↦ CANCELLEDV) ∨
   (* Both have come; nothing interesting can happen now. *)
   (∃ (f: bool), own γ (● ((None, None), Some (to_agree f)))))%I.

Definition is_asym_rendezvous γ v P :=
  (∃ (ℓ: loc), ⌜v = #ℓ⌝ ∧ inv N (asym_rendezvous_inv P ℓ γ))%I.

Theorem init_exchange_spec ℓ P:
    {{{ ∃ v, ℓ ↦ v }}}
      init_exchange #ℓ
    {{{ γ, RET #(); is_asym_rendezvous γ #ℓ P ∗
                                        fetch_permit γ ∗ pass_permit γ }}}.
Proof.
  iIntros (Φ) "Hℓ HPost".
  wp_lam.
  iDestruct "Hℓ" as (v) "Hℓ".
  rewrite -wp_fupd.
  wp_store.
  iMod (own_alloc (● ((Excl' (), Excl' ()), None) ⋅
                     ◯ (Excl' (), None, None) ⋅
                     ◯ (None, Excl' (), None))) as (γ) "HOwn".
  1: {
    apply auth_valid_discrete; simpl.
    repeat (split; try done).
    eexists; split.
    done.
    split; try done.
  }
  repeat rewrite own_op.
  iDestruct "HOwn" as "[[HOwn Hfetch] Hpass]".
  iMod (inv_alloc N _ (asym_rendezvous_inv P ℓ γ) with "[Hℓ HOwn]") as "HInv".
  {
    iNext. rewrite /asym_rendezvous_inv.
    eauto with iFrame.
  }
  iModIntro. iApply "HPost".
  rewrite /is_asym_rendezvous. iFrame. iExists _. iSplit; done.
Qed.

Theorem await_spec γ r P:
    {{{ is_asym_rendezvous γ r P ∗ fetch_permit γ }}}
      await r
    {{{ sm, RET sm; P sm ∗ passed γ }}}.
Proof.
  iIntros (Φ) "[#HIsR Hfp] HPost".
  iDestruct "HIsR" as (ℓ) "[% #HInv]". subst.
  iLöb as "IH". wp_lam. wp_bind (!_)%E.
  iInv N as "HInvO" "HInvC".
  iDestruct "HInvO" as "[[>HOwn Hℓ]|[[>HOwn Hℓ]|[[>HOwn Hℓ]|H]]]".
  - wp_load.
    iMod ("HInvC" with "[HOwn Hℓ]") as "_"; first by iLeft; iFrame.
    iModIntro.
    wp_pures.
    by iApply ("IH" with "Hfp").
  - iDestruct "Hℓ" as (v) "[Hℓ HP]".
    wp_load.
    iMod (own_update_2 with "HOwn Hfp") as "[HOwn Hpassed]".
    {
      apply transitivity with (y:=(● (None, None, Some (to_agree false)))).
      - apply auth_update_dealloc.
        apply local_update_unital_discrete.
        intros z HValid HEq.
        split; auto.
        destruct z as [[z1 z2] z3]; simpl in *.
        inversion HEq as [[HEq1 HEq2] HEq3]; simpl in *.
        destruct z1.
        {
          inversion HEq1 as [x y HContra|]. subst.
          inversion HContra.
        }
        done.
      - apply auth_update_core_id with (b := (None, None, Some (to_agree false))).
        apply pair_core_id; apply _.
        done.
    }
    iMod ("HInvC" with "[HOwn Hℓ]") as "_".
    {
      repeat iRight.
      eauto.
    }
    iModIntro.
    wp_pures.
    iApply "HPost".
    iFrame.
  - rewrite /fetch_permit.
    iDestruct (own_valid_2 with "HOwn Hfp") as %HH.
    apply auth_valid_discrete in HH; simpl in HH.
    exfalso.
    inversion HH as [_ [a [HAgr [HLe HVal]]]].
    apply to_agree_inj in HAgr.
    destruct a as [[u u'] u0].
    inversion HAgr as [[HAgr' _] _].
    inversion HAgr'; simpl in *; subst.
    inversion HLe as [x [[HContra _] _]].
    destruct x as [[xu xu'] xu0].
    simpl in *.
    destruct xu; by inversion HContra.
  - iDestruct "H" as (f) ">HOwn".
    rewrite /fetch_permit.
    iDestruct (own_valid_2 with "HOwn Hfp") as %HH.
    apply auth_valid_discrete in HH; simpl in HH.
    exfalso.
    inversion HH as [_ [a [HAgr [HLe HVal]]]].
    apply to_agree_inj in HAgr.
    destruct a as [[u u'] u0].
    inversion HAgr as [[HAgr' _] _].
    inversion HAgr'; simpl in *; subst.
    inversion HLe as [x [[HContra _] _]].
    destruct x as [[xu xu'] xu0].
    simpl in *.
    destruct xu; by inversion HContra.
Qed.

(*
  await_interruptibly_spec Ni γi handle N γ r P:
    {{{ is_interrupt_handle Ni γi handle ∗
                            is_asym_rendezvous N γ r P ∗
                            fetch_permit γ }}}
      await_interruptibly handle r
    {{{ sm, RET sm; (∃ v, ⌜sm = (#false, RESUMEDV v)%V⌝ ∧ P v ∗ passed γ) ∨
                    (∃ v, ⌜sm = (#true, RESUMEDV v)%V⌝ ∧ P v ∗ passed γ ∗
                                                           interrupted γi) ∨
                    (⌜sm = (#true, NONEV)%V⌝ ∧ cancelled γ)
    }}};
  pass_spec N γ r P v:
    {{{ is_asym_rendezvous N γ r P ∗ pass_permit γ ∗ P v }}}
      pass r v
    {{{ sm, RET sm; ⌜sm = NONEV⌝ ∧ passed γ ∨
                                    ⌜sm = CANCELLEDV⌝ ∧ P v ∗ cancelled γ}}}
*)

End asym_rendezvous_proof.
