From iris.base_logic.lib Require Export invariants.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation lang.
From iris.program_logic Require Export atomic.

Definition new_handle: val := λ: <>, ref #0%nat.

Definition interrupt: val := λ: "H", "H" <- #1%nat.

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
  #[(*GFunctor (exclR unitO);*) GFunctor (authR mnatUR)].

Instance subG_interruptiblyΣ {Σ} : subG interruptiblyΣ Σ -> interruptiblyG Σ.
Proof. solve_inG. Qed.

Section interruptibly_proof.

Context `{heapG Σ} `{interruptiblyG Σ} (N: namespace).

Definition interrupt_handle_inv γ (H: val) :=
  (∃ (ℓ: loc), ⌜H = #ℓ⌝ ∧
               ∃ (n: nat), ℓ ↦ #n ∗ own γ (● (n: mnatUR)) ∧
                           ⌜n <= 2⌝)%I.

Definition is_interrupt_handle γ H :=
  inv N (interrupt_handle_inv γ H).

Definition interrupted γ := own γ (◯ (2%nat : mnatUR)).

Definition interrupt_sent γ := own γ (◯ (1%nat : mnatUR)).

Global Instance is_interrupt_handle_persistent γ handle:
  Persistent (is_interrupt_handle γ handle).
Proof. apply _. Qed.

Global Instance interrupted_persistent γ: Persistent (interrupted γ).
Proof. apply _. Qed.

Global Instance interrupt_sent_persistent γ: Persistent (interrupt_sent γ).
Proof. apply _. Qed.

Lemma wait_fail_spec : forall γ handle (b e: val),
  {{{ is_interrupt_handle γ handle ∗ interrupt_sent γ }}}
    wait handle b e
  {{{ RET (InjLV #()); True }}}.
Proof.
  intros.
  iIntros "[#IntHInv #IntSent] HPost".
  rewrite /is_interrupt_handle /interrupt_sent /wait.
  rewrite /interrupt_handle_inv. wp_pures. wp_bind (!_)%E.
  iInv N as "HInv" "HClose".
  iDestruct "HInv" as (ℓ) "[>% Hn]".
  iDestruct "Hn" as (n) "[Hℓ [HOwn >%]]".
  subst.
  wp_load.
  destruct n.
  - iDestruct (own_valid_2 with "HOwn IntSent") as %Hv.
    apply auth_valid_discrete in Hv; simpl in *.
    rewrite ucmra_unit_left_id in Hv.
    destruct Hv as [_ [a [Contra1 [Contra2 _]]]].
    apply to_agree_inj in Contra1.
    inversion Contra1; subst.
    apply mnat_included in Contra2.
    inversion Contra2.
  - iMod ("HClose" with "[Hℓ HOwn]") as "_"; first by eauto 10 with iFrame.
    iModIntro.
    wp_pures.
    wp_bind (_ <- _)%E.
    iInv N as "HInv" "HClose".
    iDestruct "HInv" as (ℓ') "[>% Hn]".
    iDestruct "Hn" as (n') "[Hℓ [HOwn >%]]".
    inversion H1; subst.
    admit.
Admitted.

Lemma wait_spec : forall γ P Q handle (b e: val),
  {{{ is_interrupt_handle γ handle ∗ P ∗
    ({{{ P }}}
      (b e)%V
    {{{ r, RET r; ⌜r = InjLV #()⌝ ∧ P ∨ (∃ (v: val), ⌜r = InjRV v⌝) ∧ Q }}})
  }}}
    wait handle b e
  {{{ r, RET r; ⌜r = InjLV #()⌝ ∧ P ∧ interrupted γ ∨
                                        (∃ (v: val), ⌜r = InjRV v⌝ ∧ Q)}}}.
Proof.
  intros.
  iIntros "[#IntHInv [HP #Hbe]]"; rewrite /is_interrupt_handle.
  iIntros "HPost".
  iLöb as "IH". wp_lam. wp_pures.
  wp_bind (!_)%E.
  iInv N as "HInv" "HClose".
  rewrite /interrupt_handle_inv.
  iDestruct "HInv" as (ℓ) "[>% Hn]"; subst.
  iDestruct "Hn" as (n) "[Hℓ [HOwn >%]]".
  wp_load.
  destruct n.
  all: iMod ("HClose" with "[Hℓ HOwn]") as "_"; first by eauto 10 with iFrame.
  all: iModIntro; wp_pures.
  - wp_bind (b e).
    (* It can't infer Φ for some reason; applying it manually. *)
    iSpecialize ("Hbe" $! (fun v => wp NotStuck top (
      match: v with InjL <> => wait #ℓ b e | InjR "v" => InjR "v" end) Φ )).
    wp_apply ("Hbe" with "HP").
    iIntros (r) "H".
    iDestruct "H" as "[[% HP]|[HR Q]]"; subst.
    * wp_pures.
      by wp_apply ("IH" with "HP").
    * iDestruct "HR" as (v) "%"; subst.
      wp_pures.
      iApply "HPost".
      eauto.
  - wp_bind (_ <- _)%E.
    iInv N as "HInv" "HClose".
    iDestruct "HInv" as (ℓ') "[>% Hn]"; subst.
    inversion H2; subst.
    iDestruct "Hn" as (n') "[Hℓ [HOwn >%]]".
    wp_store.
    iMod (own_update with "HOwn") as "[HOwn HFrag]".
    {
      apply (auth_update_alloc _ (2%nat: mnatUR) (2%nat: mnatUR)).
      apply mnat_local_update.
      lia.
    }
    iMod ("HClose" with "[Hℓ HOwn]") as "_"; first by eauto 10 with iFrame.
    iModIntro.
    wp_pures.
    iApply "HPost".
    iLeft.
    rewrite /interrupted.
    eauto with iFrame.
Qed.

End interruptibly_proof.
