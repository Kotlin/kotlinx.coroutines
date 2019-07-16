From iris.program_logic Require Export weakestpre.
From iris.base_logic.lib Require Export invariants.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode.
From iris.heap_lang Require Import notation lang.
From iris.algebra Require Import cmra.
Require Import SegmentQueue.lib.thread_queue.thread_queue_spec.
Require Import SegmentQueue.algebra.bounded_pos.
Require Import SegmentQueue.lib.semaphore.semaphore_spec.
Require Import SegmentQueue.lib.semaphore.semaphore_impl.

Section proof.

  Class mSemaphoreG Σ := MSemaphoreG { msemaphore_inG :> inG Σ boundedPosR }.
  Definition mSemaphoreΣ : gFunctors := #[GFunctor boundedPosR].
  Instance subG_msemaphoreΣ {Σ} : subG mSemaphoreΣ Σ -> mSemaphoreG Σ.
  Proof. solve_inG. Qed.

  Context `{mSemaphoreG Σ}.
  Context `{heapG Σ}.
  Notation iProp := (iProp Σ).

  Variable tq : threadQueue.
  Variable (N: namespace).

  Definition permit_sq (γ: gname) (perms : nat) :=
    own γ (bpos 1 (Pos.of_nat (1 + perms))).

  Definition semaphore_inv γ (z : val) (ℓ pℓ : loc) (perms : nat) (R : iProp) : iProp :=
    (∃ (p : Z), ℓ ↦ z ∗ pℓ ↦ #p ∗
                ((∃ n, ⌜p = (1 + Z.of_nat n)%Z⌝ ∧
                       iPropPow (S n) R ∗ iPropPow (S n) (own γ (bpos 1 (Pos.of_nat (S perms))))) ∨
                 ⌜(p <= 0)%Z⌝))%I.

  Definition is_semaphore_sq
             (N : namespace)
             (γ: gname)
             (semaphore: val)
             (perms: nat)
             (R: iProp) :=
    (∃ (ℓ pℓ: loc) (q : val), ⌜semaphore = #ℓ⌝ ∧
                           (∃ γ', is_thread_queue tq N γ' q (permit_sq γ perms ∗ R)) ∧
                           inv N (semaphore_inv γ (#pℓ, q) ℓ pℓ perms R))%I.

  Global Instance is_semaphore_persistent_sq γ sem p R:
    Persistent (is_semaphore_sq N γ sem p R).
  Proof. apply _. Qed.

  Global Instance permit_timeless_sq γ p : Timeless (permit_sq γ p).
  Proof. apply _. Qed.

  Global Instance iPropPow_ne Σ n: NonExpansive (@iPropPow Σ n).
  Proof. induction n; solve_proper. Qed.

  Global Instance semaphore_inv_ne γ z ℓ pℓ perms: NonExpansive (semaphore_inv γ z ℓ pℓ perms).
  Proof. solve_proper. Qed.

  Global Instance is_semaphore_ne_sq N γ sem p: NonExpansive (is_semaphore_sq N γ sem p).
  Proof. solve_proper. Qed.

  Theorem permit_k_exclusive_sq γ p:
      iPropPow (1 + p) (permit_sq γ p) -∗ False.
  Proof.
    iIntros "HPerms".
    unfold permit_sq.
    assert (forall k, (iPropPow (S k) (own γ (bpos 1 (Pos.of_nat (S p)))))
                   -∗ own γ (bpos (Pos.of_nat (S k)) (Pos.of_nat (S p)))).
    {
      iIntros (k) "H".
      iInduction k as [|k'] "Hk"; first by iDestruct "H" as "[HOwn _]".
      simpl in *.
      iDestruct "H" as "[HOwn1 [HOwn2 HIx]]".
      replace (Pos.of_nat (S (S k'))) with (1 + Pos.of_nat (S k'))%positive.
      2: {
        replace (S (S k')) with (1 + S k')%nat by auto.
        by rewrite Nat2Pos.inj_add.
      }
      rewrite bpos_split.
      rewrite own_op.
      iFrame.
      iApply "Hk".
      iFrame.
    }
    iAssert (own γ (bpos (Pos.of_nat (S p)) (Pos.of_nat (S p)))) with "[HPerms]" as "Hγ";
      first by iApply H1.
    iDestruct (own_valid γ with "Hγ") as %Contra.
    unfold valid in Contra.
    unfold cmra_valid in Contra.
    simpl in Contra.
    apply Is_true_eq_true in Contra.
    apply Pos.ltb_lt in Contra.
    lia.
  Qed.

  Theorem new_semaphore_spec_sq : forall p R,
    {{{ iPropPow p R }}}
      new_semaphore_sq tq #p
    {{{ sm γ, RET sm; is_semaphore_sq N γ sm p R}}}.
  Proof.
    intros p R.
    iIntros (Φ) "HR Post".
    rewrite -wp_fupd /new_semaphore_sq /=.
    wp_lam.
    wp_bind (new_thread_queue tq #()).
    destruct p as [|p'].
    1: remember 0%nat as p.
    2: remember (S p') as p.
    1: iMod (own_alloc (bpos xH (Pos.of_nat 2))%Qp) as (γ) "Hγ"; first done.
    2: iMod (own_alloc (bpos (Pos.of_nat p) (Pos.of_nat (S p)))%Qp) as (γ) "Hγ".
    2: {
      rewrite /valid /cmra_valid.
      simpl.
      apply Is_true_eq_left.
      apply Pos.ltb_lt.
      replace (Pos.of_nat (S p)) with (1 + Pos.of_nat p)%positive.
      2: {
        replace (S p) with (1 + p)%nat by trivial.
        subst.
        rewrite Nat2Pos.inj_add; auto.
      }
      lia.
    }
    all: wp_apply (new_thread_queue_spec _ N (permit_sq γ p ∗ R)%I); first done.
    all: iIntros (qq γt) "itq".
    all: wp_bind (ref #p)%E.
    all: wp_alloc pl as "Hpl".
    all: wp_pure _.
    all: wp_alloc l as "Hl".
    all: iMod (inv_alloc N _ (semaphore_inv γ (#pl, qq) l pl p R) with "[Hpl Hγ HR Hl]") as "#HInv".

    2, 4: iApply "Post".
    2, 3: repeat (iExists _).
    all: eauto; iNext; unfold semaphore_inv.
    all: iExists _; iFrame.
    * iRight.
      iPureIntro.
      lia.
    * iLeft.
      subst.
      iExists p'.
      iSplit.
      { iPureIntro. lia. }
      { iFrame.
        remember (Pos.of_nat (S (S p'))) as m.
        clear.
        iInduction p' as [|p''] "Hp'"; simpl; iFrame.
        replace (S (S p'')) with (1 + S p'')%nat by trivial.
        rewrite Nat2Pos.inj_add; auto.
        rewrite bpos_split.
        rewrite own_op.
        replace (Pos.of_nat 1) with 1%positive by auto.
        iDestruct "Hγ" as "[Hown Hγ]".
        iFrame.
        iApply "Hp'".
        auto.
      }
  Qed.

  Theorem try_acquire_spec_sq : forall γ sm p R,
    {{{ is_semaphore_sq N γ sm p R }}}
      FAA (Fst !sm) #(-1)
    {{{ pz, RET #(pz); ((permit_sq γ p ∗ R) ∧ ⌜(0 < pz)%Z⌝) ∨ ⌜(pz <= 0)%Z⌝ }}}.
  Proof.
    iIntros (γ sm p R Φ) "HIsSem HPerm".
    unfold is_semaphore_sq.
    iDestruct "HIsSem" as (ℓ pℓ q) "[% [#Htq #Hpt]]"; subst.
    wp_bind (! #ℓ)%E.
    iInv N as (p') "[HH HR]" "HClose".
    wp_load.
    iMod ("HClose" with "[-HPerm]") as "_".
    { iNext. iExists p'. iFrame. }
    iModIntro.
    wp_pure _.
    iInv N as (p'') "[Hℓ [Hpℓ Hn]]" "HClose".
    wp_faa.
    iApply "HPerm".
    iDestruct "Hn" as "[HN1|%]".
    2: {
      iRight.
      iMod ("HClose" with "[-]") as "_".
      2: by auto.
      iNext.
      unfold semaphore_inv.
      iExists (p'' + -1)%Z.
      iFrame.
      iRight.
      iPureIntro.
      lia.
    }
    - iDestruct "HN1" as (n) "HN".
      iDestruct "HN" as "[% [[HR HRs] [Hγ Hγs]]]". subst.
      iLeft.
      iMod ("HClose" with "[- Hγ HR]") as "_".
      2: {
        iFrame.
        iPureIntro.
        lia.
      }
      iNext.
      unfold semaphore_inv.
      iExists n.
      replace (1 + n + -1)%Z with (Z.of_nat n)%Z by lia.
      iFrame.
      destruct n; first by auto.
      iLeft.
      iExists n.
      iFrame.
      iPureIntro.
      lia.
  Qed.

  Theorem acquire_spec_sq : forall γ sm p R,
    {{{ is_semaphore_sq N γ sm p R }}}
      acquire_sq tq sm
    {{{ RET #(); permit_sq γ p ∗ R }}}.
  Proof.
    iIntros (γ sm p R Φ) "#HIsSem HPerm".
    wp_lam.
    wp_bind (FAA (Fst ! sm) #(-1)).
    wp_apply (try_acquire_spec_sq with "HIsSem").
    iIntros (pz) "Hp".
    wp_let.
    wp_bind (! sm)%E.
    unfold is_semaphore_sq.
    iDestruct "HIsSem" as (ℓ pℓ q) "[% #[Hpt HInv]]"; subst.
    iInv N as (p') "[Hℓ [Hpℓ Hr]]" "HClose".
    wp_load.
    iMod ("HClose" with "[-HPerm Hp]") as "_".
    { iNext; iExists p'; iFrame. }
    iModIntro.
    wp_pure _.
    wp_let.
    wp_bind (_ < _)%E.
    wp_op.
    iDestruct "Hpt" as (γt) "Hpt".
    iDestruct "Hp" as "[Hp|%]".
    - iDestruct "Hp" as "[Hp %]".
      replace (bool_decide (0 < pz)%Z) with true.
      2: {
        rewrite bool_decide_eq_true_2; auto.
      }
      wp_if.
      iApply "HPerm".
      iFrame.
    - replace (bool_decide (0 < pz)%Z) with false.
      2: {
        rewrite bool_decide_eq_false_2; auto; lia.
      }
      wp_if.
      wp_apply (add_to_queue_and_suspend_spec tq); auto.
  Qed.

  Theorem try_release_spec_sq : forall γ sm p R,
    {{{ is_semaphore_sq N γ sm p R ∗ permit_sq γ p ∗ R }}}
      FAA (Fst !sm) #1
    {{{ pz, RET #(pz); (⌜(0 <= pz)%Z⌝) ∨ (permit_sq γ p ∗ R) ∧ ⌜(pz < 0)%Z⌝ }}}.
  Proof.
    iIntros (γ sm p R Φ) "[#HIsSem [HPerm HR]] HPost".
    iDestruct "HIsSem" as (ℓ pℓ q) "[% [#Htq #HInv]]"; subst.
    iDestruct "Htq" as (γt) "#Htq".
    wp_bind (!#ℓ)%E.
    iInv N as (p') "[Hℓ [Hpℓ Hps]]" "HClose".
    wp_load.
    iMod ("HClose" with "[Hℓ Hpℓ Hps]") as "_".
    { iExists p'. iFrame. }
    clear p'.
    iModIntro.
    wp_pure _.
    iInv N as (p') "[Hℓ [Hpℓ Hps]]" "HClose".
    wp_faa.
    iApply "HPost".
    iDestruct "Hps" as "[HN1|%]".
    - iLeft.
      iDestruct "HN1" as (n) "[% [HRs Hγs]]".
      iMod ("HClose" with "[-]") as "_".
      2: iPureIntro; lia.
      simpl.
      iNext.
      iExists _; iFrame.
      iLeft.
      iExists (1+n)%nat.
      iFrame.
      iPureIntro; lia.
    - destruct p'.
      * iLeft.
        iMod ("HClose" with "[-]") as "_".
        2: iPureIntro; lia.
        iNext. iExists _. iFrame. iLeft. iExists 0%nat; simpl.
        iFrame.
        iPureIntro.
        lia.
      * lia.
      * iRight.
        iMod ("HClose" with "[- HPerm HR]") as "_".
        {
          iNext. iExists _. simpl. iFrame. iRight. iPureIntro. lia.
        }
        iFrame.
        auto.
  Qed.

  Theorem release_spec_sq: forall γ sm p R,
      {{{ is_semaphore_sq N γ sm p R ∗ permit_sq γ p ∗ R }}}
      release_sq tq sm
    {{{ RET #(); True }}}.
  Proof.
    iIntros (γ sm p R Φ) "[#HIsSem [HPerm HR]] HPost".
    wp_lam.
    wp_bind (FAA _ _).
    wp_apply (try_release_spec_sq with "[HPerm HR]").
    {
      iFrame.
      iSplitR "HR"; iAssumption.
    }
    iIntros (pz) "He".
    wp_let.
    iDestruct "HIsSem" as (ℓ pℓ q) "[% [#Htq #HInv]]"; subst.
    iDestruct "Htq" as (γt) "#Htq".
    wp_bind (!#ℓ)%E.
    iInv N as (p') "[Hℓ [Hpℓ Hps]]" "HClose".
    wp_load.
    iMod ("HClose" with "[Hℓ Hpℓ Hps]") as "_".
    { iNext; iExists _; iFrame. }
    clear p'.
    iModIntro.
    wp_pure _.
    wp_let.
    wp_pure _.
    iDestruct "He" as "[% | [[HPerm HR] %]]".
    - replace (bool_decide _) with true.
      2: by (rewrite bool_decide_eq_true_2; auto).
      wp_if. iApply "HPost". auto.
    - replace (bool_decide _) with false.
      2: rewrite bool_decide_eq_false_2; auto; lia.
      wp_if.
      wp_apply (resume_next_from_queue_spec tq with "[HPerm HR]"); auto.
      iSplitL ""; auto.
      iFrame.
  Qed.

End proof.

Section spec.

  Context `{mSemaphoreG Σ}.
  Context `{heapG Σ}.
  Notation iProp := (iProp Σ).
  Variable tq : threadQueue.

  Canonical Structure semaphore_sq `{!heapG Σ, !mSemaphoreG Σ} :=
    {| is_semaphore_persistent:= is_semaphore_persistent_sq tq;
       is_semaphore_ne := is_semaphore_ne_sq tq;
       permit_timeless := permit_timeless_sq;
       permit_k_exclusive := permit_k_exclusive_sq;
       new_semaphore_spec := new_semaphore_spec_sq tq;
       acquire_spec := acquire_spec_sq tq;
       release_spec := release_spec_sq tq;
    |}.

End spec.
