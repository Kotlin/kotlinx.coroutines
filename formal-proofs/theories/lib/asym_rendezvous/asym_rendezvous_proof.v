From iris.base_logic.lib Require Export invariants.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation lang.
From iris.program_logic Require Export atomic.
From iris.bi.lib Require Import atomic.
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

Context `{heapG Σ} `{asym_rendezvousG Σ} `{interruptiblyG Σ} (N: namespace).

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

Theorem fetch_permit_exclusive γ: fetch_permit γ -∗ fetch_permit γ -∗ False.
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

Definition asym_rendezvous_inv ℓ γ P :=
   (* Neither reader no writer came yet. *)
  ((own γ (● ((Excl' (), Excl' ()), None)) ∗ ℓ ↦ NONEV) ∨
   (* The writer came and left the resource, but the reader didn't come. *)
   (own γ (● ((Excl' (), None), Some (to_agree false))) ∗ ℓ ↦ RESUMEDV ∗ P) ∨
   (* The reader came and broke the cannel; writer wasn't here. *)
   (own γ (● ((None, Excl' ()), Some (to_agree true))) ∗ ℓ ↦ CANCELLEDV) ∨
   (* Both have come; nothing interesting can happen now. *)
   (∃ (f: bool), own γ (● ((None, None), Some (to_agree f)))))%I.

Definition is_asym_rendezvous γ v P :=
  (∃ (ℓ: loc), ⌜v = #ℓ⌝ ∧ inv N (asym_rendezvous_inv ℓ γ P))%I.

Global Instance is_asym_rendezvous_persistent γ v P : Persistent (is_asym_rendezvous γ v P).
Proof. apply _. Qed.

Global Instance is_asym_rendezvous_inv_ne ℓ γ : NonExpansive (asym_rendezvous_inv ℓ γ).
Proof. solve_proper. Qed.

Global Instance is_asym_rendezvous_ne γ v : NonExpansive (is_asym_rendezvous γ v).
Proof. solve_proper. Qed.

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
  iMod (inv_alloc N _ (asym_rendezvous_inv ℓ γ P) with "[Hℓ HOwn]") as "HInv".
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
    {{{ RET #(); P ∗ passed γ }}}.
Proof.
  iIntros (Φ) "[#HIsR Hfp] HPost".
  iDestruct "HIsR" as (ℓ) "[% #HInv]". subst.
  iLöb as "IH". wp_lam. wp_bind (!_)%E.
  iInv N as "HInvO" "HInvC".
  iDestruct "HInvO" as "[[>HOwn Hℓ]|[[>HOwn [Hℓ HP]]|[[>HOwn Hℓ]|H]]]".
  - wp_load.
    iMod ("HInvC" with "[HOwn Hℓ]") as "_"; first by iLeft; iFrame.
    iModIntro.
    wp_pures.
    by iApply ("IH" with "Hfp").
  - wp_load.
    iMod (own_update_2 with "HOwn Hfp") as "[HOwn Hpassed]".
    {
      apply transitivity with (y:=(● (None, None, Some (to_agree false)))).
      - apply auth_update_dealloc.
        apply prod_local_update_1.
        apply prod_local_update_1.
        apply delete_option_local_update.
        by apply excl_exclusive.
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
  - iDestruct (own_valid_2 with "HOwn Hfp") as
        %[[[[HContra|[a [b [_ [HContra _]]]]]%option_included _]
             %prod_included _]
            %prod_included _]
         %auth_both_valid; discriminate.
  - iDestruct "H" as (f) ">HOwn".
    iDestruct (own_valid_2 with "HOwn Hfp") as
        %[[[[HContra|[a [b [_ [HContra _]]]]]%option_included _]
             %prod_included _]
            %prod_included _]
         %auth_both_valid; discriminate.
Qed.

Lemma check_rendezvous_spec γ P ℓ :
  {{{ inv N (asym_rendezvous_inv ℓ γ P) ∗ fetch_permit γ }}}
    (λ: "e", !"e")%V #ℓ
  {{{ (r: val), RET r; ⌜r = NONEV⌝ ∧ fetch_permit γ ∨
                       ⌜r = RESUMEDV⌝ ∧ (fun (_: val) => P ∗ passed γ) #0 }}}.
Proof.
  iIntros (Φ) "[#HInv Hfp] HPost".
  rewrite /asym_rendezvous_inv /fetch_permit.
  wp_pures.
  iInv N as "HInvO" "HInvC".
  iDestruct "HInvO" as "[[>HOwn Hℓ]|[[>HOwn [Hℓ HP]]|[[>HOwn Hℓ]|H]]]".
  - wp_load.
    iMod ("HInvC" with "[HOwn Hℓ]") as "_"; first by eauto with iFrame.
    iModIntro.
    iApply "HPost".
    by eauto with iFrame.
  - iMod (own_update_2 with "HOwn Hfp") as "[HOwn HPassed]".
    {
      apply transitivity with (y := ● (None, None, Some (to_agree false))).
      * apply auth_update_dealloc.
        apply prod_local_update_1.
        apply prod_local_update_1.
        apply delete_option_local_update.
        by apply excl_exclusive.
      * apply auth_update_core_id with (b := (None, None, Some (to_agree false))).
        apply pair_core_id; apply _.
        done.
    }
    wp_load.
    iMod ("HInvC" with "[HOwn Hℓ]") as "_"; first by eauto 10 with iFrame.
    iModIntro.
    iApply ("HPost" with "[HP HPassed]").
    by eauto 10 with iFrame.
  - iDestruct (own_valid_2 with "HOwn Hfp") as
        %[[[[HContra|[a [b [_ [HContra _]]]]]%option_included _]
             %prod_included _]
            %prod_included _]
         %auth_both_valid; discriminate.
  - iDestruct "H" as (f) ">HOwn".
    iDestruct (own_valid_2 with "HOwn Hfp") as
        %[[[[HContra|[a [b [_ [HContra _]]]]]%option_included _]
             %prod_included _]
            %prod_included _]
         %auth_both_valid; discriminate.
Qed.

Theorem await_interruptibly_spec Ni γi handle γ r P:
    {{{ is_interrupt_handle Ni γi handle ∗
                            is_asym_rendezvous γ r P ∗
                            fetch_permit γ }}}
      await_interruptibly handle r
    {{{ sm, RET sm; ⌜sm = (#false, RESUMEDV)%V⌝ ∧ P ∗ passed γ ∨
                    ⌜sm = (#true, RESUMEDV)%V⌝ ∧ ▷ P ∗ passed γ ∗ interrupted γi ∨
                    ⌜sm = (#true, NONEV)%V⌝ ∧ cancelled γ
    }}}.
Proof.
  iIntros (Φ) "[#HIsHandl [#HIsR Hfp]] HPost".
  iDestruct "HIsR" as (ℓ) "[% #HInv]". subst.
  rewrite /await_interruptibly /=.
  wp_lam.
  iApply (interruptibly_spec with "[Hfp]").
  2: {
    iNext.
    iIntros (r v) "[[% Hx]|[% Hx]]"; subst; iApply ("HPost" with "[Hx]").
    {
      iRight.
      instantiate (1:=(fun v => interrupted γi ∗
                               ((⌜v = InjRV #false⌝ ∧ ▷ P ∗ passed γ)
                                ∨ ⌜v = InjLV #()⌝ ∧ cancelled γ))%I).
      simpl.
      iDestruct "Hx" as "[HInt [[% [HP HPassed]]|[% HCan]]]"; subst; eauto.
    }
    {
      iLeft.
      instantiate (1:=(fun v => ⌜v = #false⌝ ∧ P ∗ passed γ)%I).
      iDestruct "Hx" as "[% [HP HPassed]]".
      subst; eauto with iFrame.
    }
  }
  { iSplit; first done.
    iSplitL; first by iApply "Hfp".
    iSplit.
    {
      iModIntro.
      iIntros (Φ') "Hfp HPost".
      iApply (check_rendezvous_spec with "[Hfp]").
      1: by iFrame.
      iNext.
      iIntros (r) "[HPre|[% [HP HPassed]]]"; iApply "HPost"; eauto 10.
    }
    {
      iModIntro.
      iIntros (Φ') "[Hfp #HIntr] HPost".
      wp_lam.
      wp_pures.
      iClear "HIsHandl".
      rewrite /fetch_permit.
      awp_apply getAndSet.getAndSet_spec without "HPost".
      iInv N as "HInvO".
      iDestruct "HInvO" as "[[>HOwn Hℓ]|[[>HOwn [Hℓ HP]]|[[>HOwn Hℓ]|H]]]".
      3: iDestruct (own_valid_2 with "HOwn Hfp") as
            %[[[[HContra|[a [b [_ [HContra _]]]]]%option_included _]
                %prod_included _]
                %prod_included _]
            %auth_both_valid; discriminate.
      3: iDestruct "H" as (f) ">HOwn";
        iDestruct (own_valid_2 with "HOwn Hfp") as
            %[[[[HContra|[a [b [_ [HContra _]]]]]%option_included _]
                %prod_included _]
                %prod_included _]
            %auth_both_valid; discriminate.
      {
        iAssert ((fun k => ▷ ℓ ↦ k ∧ ⌜val_is_unboxed k⌝) (InjLV #()))%I with "[Hℓ]" as "HII".
        1: by iFrame.
        iAaccIntro with "HII".
        {
          iIntros "[Hℓ _]".
          iModIntro.
          iFrame.
          rewrite /asym_rendezvous_inv.
          eauto 10 with iFrame.
        }
        {
          iIntros "Hℓ".
          iMod (own_update_2 with "HOwn Hfp") as "[HOwn HCancelled]".
          {
            apply transitivity with (y:= ● (None, Excl' (), None)).
            - apply auth_update_dealloc.
              apply prod_local_update_1.
              apply prod_local_update_1.
              apply delete_option_local_update.
              apply excl_exclusive.
            - apply auth_update_alloc with
                  (b' := (None, None, Some (to_agree true))).
              apply prod_local_update_2.
              apply alloc_option_local_update.
              done.
          }
          iModIntro.
          iSplitL "Hℓ HOwn".
          {
            rewrite /asym_rendezvous_inv.
            by eauto 10 with iFrame.
          }
          {
            iIntros "HPost".
            iApply "HPost".
            eauto 10 with iFrame.
          }
        }
      }
      {
        iAssert ((fun k => ▷ ℓ ↦ k ∧ ⌜val_is_unboxed k⌝) (InjRV #false))%I with "[Hℓ]" as "HII".
        1: by iFrame.
        iAaccIntro with "HII".
        {
          iIntros "[Hℓ _]".
          iModIntro.
          iFrame.
          rewrite /asym_rendezvous_inv.
          eauto 10 with iFrame.
        }
        {
          iIntros "Hℓ".
          iMod (own_update_2 with "HOwn Hfp") as "[HOwn HPassed]".
          {
            apply transitivity with (y := ● (None, None, Some (to_agree false))).
            - apply auth_update_dealloc.
              apply prod_local_update_1.
              apply prod_local_update_1.
              apply delete_option_local_update.
              apply excl_exclusive.
            - apply auth_update_core_id with (b := (None, None, Some (to_agree false))).
              1: apply pair_core_id; by apply _.
              done.
          }
          iModIntro.
          iSplitR "HP HPassed".
          2: {
            iIntros "HPost".
            iApply "HPost".
            rewrite /passed.
            iSplitR; eauto.
          }
          iNext.
          rewrite /asym_rendezvous_inv.
          eauto 10 with iFrame.
        }
      }
    }
  }
Qed.

Theorem pass_spec γ r P:
    Laterable P ->
    {{{ is_asym_rendezvous γ r P ∗ pass_permit γ ∗ P }}}
      pass r
    {{{ sm, RET sm; ⌜sm = NONEV⌝ ∧ passed γ ∨
                    ⌜sm = CANCELLEDV⌝ ∧ P ∗ cancelled γ}}}.
Proof.
  iIntros (HLat Φ) "[#HIsR [Hpp HP]] HPost".
  iDestruct "HIsR" as (ℓ) "[% #HInv]". subst.
  rewrite /pass_permit.
  wp_lam.
  awp_apply getAndSet.getAndSet_spec without "HPost".
  iInv N as "HInvO".
  iDestruct "HInvO" as "[[>HOwn Hℓ]|[[>HOwn [Hℓ _]]|[[>HOwn Hℓ]|H]]]".
  2: iDestruct (own_valid_2 with "HOwn Hpp") as
      %[[[_ [HContra|[a [b [_ [HContra _]]]]]%option_included]
           %prod_included _]
          %prod_included _]
       %auth_both_valid; discriminate.
  3: {
    iDestruct "H" as (f) ">HOwn".
    iDestruct (own_valid_2 with "HOwn Hpp") as
      %[[[_ [HContra|[a [b [_ [HContra _]]]]]%option_included]
           %prod_included _]
          %prod_included _]
       %auth_both_valid; discriminate.
  }
  {
    iAssert ((fun k => ▷ ℓ ↦ k ∧ ⌜val_is_unboxed k⌝) (InjLV #()))%I with "[Hℓ]" as "HII".
    1: by iFrame.
    iAaccIntro with "HII".
    {
      iFrame.
      iIntros "[Hℓ _]".
      iModIntro.
      iNext.
      rewrite /asym_rendezvous_inv.
      eauto 10 with iFrame.
    }
    {
      iIntros "Hℓ".
      iMod (own_update_2 with "HOwn Hpp") as "[HOwn HPassed]".
      {
        apply transitivity with (y := ● (Excl' (), None, None)).
        - apply auth_update_dealloc.
          apply prod_local_update_1.
          apply prod_local_update_2.
          apply delete_option_local_update.
          apply excl_exclusive.
        - apply auth_update_alloc with (b' := (None, None, Some (to_agree false))).
          apply prod_local_update_2.
          apply alloc_option_local_update.
          done.
      }
      iModIntro.
      iSplitR "HPassed".
      {
        iNext.
        rewrite /asym_rendezvous_inv.
        eauto 10 with iFrame.
      }
      {
        rewrite /passed.
        iIntros "HPost".
        iApply "HPost".
        eauto.
      }
    }
  }
  {
    iAssert ((fun k => ▷ ℓ ↦ k ∧ ⌜val_is_unboxed k⌝) (InjRV #true))%I with "[Hℓ]" as "HII".
    1: by iFrame.
    iAaccIntro with "HII".
    {
      iFrame.
      iIntros "[Hℓ _]".
      iModIntro.
      iNext.
      rewrite /asym_rendezvous_inv.
      eauto 10 with iFrame.
    }
    {
      iIntros "Hℓ".
      iMod (own_update_2 with "HOwn Hpp") as "[HOwn HCancelled]".
      {
        apply transitivity with (y := ● (None, None, Some (to_agree true))).
        - apply auth_update_dealloc.
          apply prod_local_update_1.
          apply prod_local_update_2.
          apply delete_option_local_update.
          apply excl_exclusive.
        - apply auth_update_core_id with (b := (None, None, Some (to_agree true))).
          { apply pair_core_id; apply _. }
          done.
      }
      iModIntro.
      iSplitR "HP HCancelled".
      {
        iNext.
        rewrite /asym_rendezvous_inv.
        eauto 10 with iFrame.
      }
      {
        iIntros "HPost".
        iApply "HPost".
        rewrite /cancelled.
        iRight.
        eauto 10 with iFrame.
      }
    }
  }
Qed.

End asym_rendezvous_proof.

Section spec.

  Context `{heapG Σ}.
  Context `{interruptiblyG Σ}.
  Context `{asym_rendezvousG Σ}.

  Canonical Structure asym_rendezvous_sq `{!heapG Σ, !interruptiblyG Σ, !asym_rendezvousG Σ} :=
    {|
      asym_rendezvous_spec.is_asym_rendezvous := is_asym_rendezvous;
      asym_rendezvous_spec.is_asym_rendezvous_ne := is_asym_rendezvous_ne;
      asym_rendezvous_spec.is_asym_rendezvous_persistent := is_asym_rendezvous_persistent;
      asym_rendezvous_spec.fetch_permit := fetch_permit;
      asym_rendezvous_spec.await := await;
      asym_rendezvous_spec.await_interruptibly := await_interruptibly;
      asym_rendezvous_spec.fetch_permit_timeless := fetch_permit_timeless;
      asym_rendezvous_spec.pass_permit_timeless := pass_permit_timeless;
      asym_rendezvous_spec.cancelled_persistent := cancelled_persistent;
      asym_rendezvous_spec.passed_persistent := passed_persistent;
      asym_rendezvous_spec.pass_permit_exclusive := pass_permit_exclusive;
      asym_rendezvous_spec.cancelled_not_passed := cancelled_not_passed;
      asym_rendezvous_spec.init_exchange_spec := init_exchange_spec;
      asym_rendezvous_spec.await_interruptibly_spec := await_interruptibly_spec;
      asym_rendezvous_spec.await_spec := await_spec;
      asym_rendezvous_spec.pass_spec := pass_spec;
      asym_rendezvous_spec.fetch_permit_exclusive := fetch_permit_exclusive;
    |}.

End spec.
