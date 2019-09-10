From iris.base_logic.lib Require Export invariants.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation lang.
From iris.program_logic Require Export atomic.

Definition new_handle: val := λ: <>, ref #0%nat.

Definition interrupt: val := λ: "H", CAS "H" #0%nat #1%nat ;; #().

Definition wait: val :=
  rec: "wait" "H" "b" "e" := if: !"H" = #0%nat
                             then match: "b" "e" with
                                    NONE => "wait" "H" "b" "e"
                                  | SOME "v" => SOME "v"
                                  end
                             else "H" <- #2%nat ;; NONE.

Definition interruptibly: val :=
  λ: "H" "b" "h" "e",
  match: wait "H" "b" "e" with
    NONE => (#true, "h" "e")
  | SOME "v" => (#false, SOME "v")
  end.

Notation "'loop:' b 'interrupted:' h" :=
  (λ: "H", interruptibly "H" b h)%V (at level 100): expr_scope.

From iris.algebra Require Import cmra excl auth.

Class interruptiblyG Σ := InterruptiblyG {
  (* interruptibly_ownerG :> inG Σ (exclR unitO); *)
  interruptibly_stateG :> inG Σ (authR mnatUR);
}.

Definition interruptiblyΣ : gFunctors :=
  #[GFunctor (authR mnatUR)].

Instance subG_interruptiblyΣ {Σ} : subG interruptiblyΣ Σ -> interruptiblyG Σ.
Proof. solve_inG. Qed.

Section interruptibly_proof.

Context `{heapG Σ} `{interruptiblyG Σ} (N: namespace).

Definition interrupt_handle_inv γ (ℓ: loc) :=
  (∃ (n: nat), ℓ ↦ #n ∗ own γ (● (n: mnatUR)) ∧ ⌜n <= 2⌝)%I.

Definition is_interrupt_handle γ H :=
  (∃ (ℓ: loc), ⌜H = #ℓ⌝ ∧ inv N (interrupt_handle_inv γ ℓ))%I.

Definition interrupted γ := own γ (◯ (2%nat : mnatUR)).

Definition interrupt_sent γ := own γ (◯ (1%nat : mnatUR)).

Global Instance is_interrupt_handle_persistent γ handle:
  Persistent (is_interrupt_handle γ handle).
Proof. apply _. Qed.

Global Instance interrupted_persistent γ: Persistent (interrupted γ).
Proof. apply _. Qed.

Global Instance interrupt_sent_persistent γ: Persistent (interrupt_sent γ).
Proof. apply _. Qed.

Lemma interruptibly_wait_fail_spec : forall γ handle (b e: val),
  {{{ is_interrupt_handle γ handle ∗ interrupt_sent γ }}}
    wait handle b e
  {{{ RET (InjLV #()); True }}}.
Proof.
  iIntros (γ handle b e Φ) "[#IntHInv #IntSent] HPost". wp_lam. wp_pures.
  iDestruct "IntHInv" as (ℓ) "[-> IntHInv]". rewrite /interrupt_handle_inv.
  wp_bind (!_)%E.
  iInv N as (n) "(Hℓ & HOwn & >%)" "HClose".
  wp_load.
  destruct n.
  by iDestruct (own_valid_2 with "HOwn IntSent")
      as %[HC%mnat_included _]%auth_both_valid; lia.

  iMod ("HClose" with "[Hℓ HOwn]") as "_"; first by eauto 10 with iFrame.
  iModIntro. wp_pures. wp_bind (_ <- _)%E.

  iInv N as (?) "(Hℓ & HOwn & >%)" "HClose".
  wp_store.
  iMod (own_update with "HOwn") as "[HOwn HFrag]".
  { apply (auth_update_alloc _ (2%nat: mnatUR) (2%nat: mnatUR)).
    apply mnat_local_update. lia. }
  iMod ("HClose" with "[Hℓ HOwn]") as "_"; first by eauto 10 with iFrame.
  iModIntro. wp_pures. by iApply "HPost".
Qed.

Lemma interruptibly_wait_spec : forall γ P Q handle (b e: val),
  {{{ is_interrupt_handle γ handle ∗ P ∗
    ({{{ P }}}
      (b e)%V
    {{{ r, RET r; ⌜r = InjLV #()⌝ ∧ P ∨ (∃ (v: val), ⌜r = InjRV v⌝ ∧ Q v) }}})
  }}}
    wait handle b e
  {{{ r, RET r; ⌜r = InjLV #()⌝ ∧ P ∧ interrupted γ ∨
                                        (∃ (v: val), ⌜r = InjRV v⌝ ∧ Q v )}}}.
Proof.
  iIntros (γ P Q handle b e Φ) "[#IntHInv [HP #Hbe]] HPost". wp_lam. wp_pures.
  iDestruct "IntHInv" as (ℓ) "[-> IntHInv]". rewrite /interrupt_handle_inv.
  iLöb as "IH". wp_bind (!_)%E.
  iInv N as (n) "[Hℓ [HOwn >%]]" "HClose".
  wp_load.
  destruct n.
  all: iMod ("HClose" with "[Hℓ HOwn]") as "_"; first by eauto 10 with iFrame.
  all: iModIntro; wp_pures.
  - wp_bind (b e). wp_apply ("Hbe" with "HP"). iIntros (r) "[[-> HP]|HR]".
    * wp_pures. wp_lam. wp_pures. by wp_apply ("IH" with "HP").
    * iDestruct "HR" as (v) "[-> HQ]". wp_pures. iApply "HPost". eauto.
  - wp_bind (_ <- _)%E.
    iInv N as (n') "[Hℓ [HOwn >%]]" "HClose".
    wp_store.
    iMod (own_update with "HOwn") as "[HOwn HFrag]".
    { apply (auth_update_alloc _ (2%nat: mnatUR) (2%nat: mnatUR)).
      apply mnat_local_update. lia. }
    iMod ("HClose" with "[Hℓ HOwn]") as "_"; first by eauto 10 with iFrame.
    iModIntro. wp_pures. iApply "HPost". iLeft. rewrite /interrupted.
    eauto with iFrame.
Qed.

Lemma interruptibly_fail_spec : forall γ P Q' handle (b h e: val),
  {{{ is_interrupt_handle γ handle ∗ P ∗ interrupt_sent γ ∗
    {{{ P }}}
      (h e)%V
    {{{ (r: val), RET r; Q' r }}}
  }}}
    interruptibly handle b h e
  {{{ (v: val), RET (#true, v)%V; Q' v }}}.
Proof.
  intros. iIntros "[#HIsInt [HP [#HIntSent #Hhe]]] HPost". wp_rec. wp_pures.
  wp_apply (interruptibly_wait_fail_spec); auto.
  iIntros "_". wp_pures. wp_bind (h e). wp_apply ("Hhe" with "HP").
  iIntros (r) "HQ'". wp_pures. by iApply "HPost".
Qed.

Lemma interruptibly_spec : forall γ P Q Q' handle (b h e: val),
  {{{ is_interrupt_handle γ handle ∗ P ∗
    {{{ P }}}
      (b e)%V
    {{{ r, RET r; ⌜r = InjLV #()⌝ ∧ P ∨ (∃ (v: val), ⌜r = InjRV v⌝ ∧ Q v) }}} ∗
    {{{ P ∗ interrupted γ }}}
      (h e)%V
    {{{ (r: val), RET r; Q' r }}}
  }}}
    interruptibly handle b h e
  {{{ r v, RET r; ⌜r = (#true, v)%V⌝ ∧ Q' v ∨ ⌜r = (#false, InjRV v)%V⌝ ∧ Q v }}}.
Proof.
  intros. iIntros "[#HIsInt [HP [#Hbe #Hhe]]] HPost". wp_rec. wp_pures.
  wp_bind (wait _ _ _). wp_apply (interruptibly_wait_spec with "[HP]").
  { iFrame "HIsInt". iSplitL. iApply "HP". iApply "Hbe". }
  iIntros (r) "[[-> [HP HIntr]] | Hr]".
  - wp_pures. wp_bind (h e). wp_apply ("Hhe" with "[HP HIntr]"); first by iFrame.
    iIntros (r) "HQ'". wp_pures. iApply "HPost". iLeft. by iFrame.
  - iDestruct "Hr" as (v) "[-> HQ]". wp_pures. iApply "HPost". iRight. by iFrame.
Qed.

Lemma new_handle_spec:
  {{{ True }}}
    new_handle #()
  {{{ γ H, RET H; is_interrupt_handle γ H }}}.
Proof.
  iIntros (Φ) "_ HPost". wp_lam.
  iMod (own_alloc (● (O: mnatUR))) as (γ) "HOwn";
    first by apply auth_auth_valid.
  rewrite -wp_fupd.
  wp_alloc ℓ as "Hℓ".
  iMod (inv_alloc N _ (interrupt_handle_inv γ ℓ) with "[HOwn Hℓ]") as "HInv".
  { iExists _; by eauto with iFrame. }
  iModIntro. iApply "HPost". iExists _. eauto.
Qed.

Lemma interrupt_spec γ handle:
  {{{ is_interrupt_handle γ handle }}}
    interrupt handle
  {{{ v, RET v; interrupt_sent γ }}}.
Proof.
  iIntros (Φ) "#HIsInt HPost".
  iDestruct "HIsInt" as (ℓ) "[-> IntHInv]". rewrite /interrupt_handle_inv.
  wp_lam. wp_bind (CmpXchg _ _ _).
  iInv N as (n) "[Hℓ [HOwn >%]]" "HClose".
  destruct n.
  - wp_cmpxchg_suc.
    iMod (own_update with "HOwn") as "[HOwn HFrag]".
    { apply (auth_update_alloc _ (1%nat: mnatUR) (1%nat: mnatUR)).
      apply mnat_local_update. lia. }
    iMod ("HClose" with "[Hℓ HOwn]") as "_". by eauto with iFrame.
    iModIntro. wp_pures. iApply "HPost". by rewrite /interrupt_sent.
  - wp_cmpxchg_fail; first done.
    iMod (own_update with "HOwn") as "[HOwn HFrag]".
    { apply (auth_update_core_id _ (1%nat: mnatUR)). apply mnat_included. lia. }
    iMod ("HClose" with "[Hℓ HOwn]") as "_". by eauto with iFrame.
    iModIntro. wp_pures. iApply "HPost". by rewrite /interrupt_sent.
 Qed.

End interruptibly_proof.
