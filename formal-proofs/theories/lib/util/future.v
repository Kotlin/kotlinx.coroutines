From iris.heap_lang Require Import notation lang.
From SegmentQueue.util Require Import cmra.

Definition emptyFuture: val :=
  λ: <>, ref (InjLV #0).

Definition completeFuture: val :=
  λ: "v", ref (InjR "v").

Definition tryCompleteFuture: val :=
  λ: "f" "v", CAS "f" (InjLV #0) (InjR "v").

Definition tryCancelFuture: val :=
  λ: "f", CAS "f" (InjLV #0) (InjLV #1).

Definition awaitFuture: val :=
  rec: "loop" "f" := match: !"f" with
                       InjL "v" => if: "v" = #0 then "loop" "f" else NONEV
                     | InjR "v" => SOME "v"
                     end.

From iris.base_logic Require Import lib.invariants.
From iris.program_logic Require Import atomic.
From iris.heap_lang Require Import proofmode.
From iris.algebra Require Import cmra excl csum auth csum numbers.

Section proof.

Inductive future_state :=
  | FutureEmpty
  | FutureCompleted (v: val)
  | FutureCancelled.

Notation permit := (optionUR (csumR fracR (agreeR unitO))).

Notation algebra := (authUR (prodUR
                               (prodUR
                                  (optionUR (agreeR (optionO valO)))
                                  permit)
                               permit)).

Class futureG Σ := FutureG {
  future_inG :> inG Σ algebra;
}.
Definition futureΣ : gFunctors := #[GFunctor algebra].
Instance subG_futureΣ {Σ} : subG futureΣ Σ -> futureG Σ.
Proof. solve_inG. Qed.

Context `{heapG Σ} `{futureG Σ} (N: namespace).

Definition permit_auth_ra (present: bool): permit :=
  Some (if present then Cinl 1%Qp else Cinr (to_agree ())).

Definition permit_state_ra (present: bool): permit :=
  Some (if present then Cinl (1 / 2)%Qp else Cinr (to_agree ())).

Definition future_auth_ra (p: leibnizO future_state): algebra :=
  ● match p with
  | FutureEmpty => (None, permit_auth_ra true, permit_auth_ra true)
  | FutureCompleted v => (Some (to_agree (Some v)), permit_auth_ra false, permit_auth_ra true)
  | FutureCancelled => (Some (to_agree None), permit_auth_ra true, permit_auth_ra false)
  end.

Definition future_completion_permit (γ: gname) (q: Qp): iProp Σ :=
  own γ (◯ (None, Some (Cinl q), None)).

Definition future_cancellation_permit (γ: gname) (q: Qp): iProp Σ :=
  own γ (◯ (None, None, Some (Cinl q))).

Definition future_is_completed (γ: gname) (v: val): iProp Σ :=
  own γ (◯ (Some (to_agree (Some v)), permit_state_ra false, None)).

Definition future_is_cancelled (γ: gname): iProp Σ :=
  own γ (◯ (Some (to_agree None), None, permit_state_ra false)).

Global Instance future_cancellation_permit_Timeless:
  Timeless (future_cancellation_permit γ q).
Proof. apply _. Qed.

Global Instance future_completion_permit_Timeless:
  Timeless (future_completion_permit γ q).
Proof. apply _. Qed.

Global Instance future_is_completed_Persistent:
  Persistent (future_is_completed γ v).
Proof. apply _. Qed.

Global Instance future_is_cancelled_Persistent:
  Persistent (future_is_cancelled γ).
Proof. apply _. Qed.

Theorem future_completion_permit_implies_not_completed γ v q:
  future_completion_permit γ q -∗ future_is_completed γ v -∗ False.
Proof.
  iIntros "H1 H2".
  iDestruct (own_valid_2 with "H1 H2") as %[[_ HValid]%pair_valid _]%pair_valid.
  exfalso. move: HValid=> /=. by compute.
Qed.

Theorem future_cancellation_permit_implies_not_cancelled γ q:
  future_cancellation_permit γ q -∗ future_is_cancelled γ -∗ False.
Proof.
  iIntros "H1 H2".
  iDestruct (own_valid_2 with "H1 H2") as %[_ HValid]%pair_valid.
  exfalso. move: HValid=> /=. by compute.
Qed.

Theorem future_is_completed_not_cancelled γ v:
  future_is_completed γ v -∗ future_is_cancelled γ -∗ False.
Proof.
  iIntros "H1 H2".
  iDestruct (own_valid_2 with "H1 H2")
    as %[[HValid _]%pair_valid _]%pair_valid.
  exfalso. move: HValid=> /=. rewrite -Some_op Some_valid=> HValid.
  by apply agree_op_invL' in HValid.
Qed.

Definition future_invariant (γ: gname) (ℓ: loc) (state: future_state): iProp Σ :=
  own γ (future_auth_ra state) ∗ match state with
    | FutureEmpty => ℓ ↦ InjLV #0
    | FutureCompleted v => ℓ ↦ InjRV v
    | FutureCancelled =>  ℓ ↦ InjLV #1
  end.

Definition is_future (γ: gname) (f: val): iProp Σ :=
  ∃ (ℓ: loc), ⌜f = #ℓ⌝ ∧ inv N (∃ state, future_invariant γ ℓ state).

Global Instance is_future_persistent γ f:
  Persistent (is_future γ f).
Proof. apply _. Qed.

Instance future_state_Inhabited: Inhabited future_state.
Proof. econstructor. econstructor. Qed.

Lemma future_is_completed_from_auth_ra γ v:
  own γ (future_auth_ra (FutureCompleted v)) ==∗
  own γ (future_auth_ra (FutureCompleted v)) ∗ future_is_completed γ v.
Proof.
  iIntros "H●". iMod (own_update with "H●") as "[$ $]"; last done.
  apply auth_update_core_id; first by apply _.
  repeat (apply prod_included; split). all: simpl. all: try done.
  apply None_least.
Qed.

Lemma future_is_cancelled_from_auth_ra γ:
  own γ (future_auth_ra FutureCancelled) ==∗
  own γ (future_auth_ra FutureCancelled) ∗ future_is_cancelled γ.
Proof.
  iIntros "H●". iMod (own_update with "H●") as "[$ $]"; last done.
  apply auth_update_core_id; first by apply _.
  repeat (apply prod_included; split). all: simpl. all: try done.
  apply None_least.
Qed.

Theorem future_is_not_unit γ f: is_future γ f -∗ ⌜f ≠ #()⌝.
Proof. iIntros "HFuture". by iDestruct "HFuture" as (?) "[-> _]". Qed.

Theorem awaitFuture_spec γ f:
  {{{ is_future γ f }}}
    awaitFuture f
  {{{ v, RET v; (∃ v', ⌜v = SOMEV v'⌝ ∧ future_is_completed γ v') ∨
                ⌜v = NONEV⌝ ∧ future_is_cancelled γ }}}.
Proof.
  iIntros (Φ) "HFuture HΦ". iDestruct "HFuture" as (ℓ ->) "#HFuture".
  wp_lam. iLöb as "IH". wp_bind (!#ℓ)%E.
  iInv "HFuture" as (p) "[>H● Hℓ]" "HInvClose".
  destruct p as [|v|]; wp_load.
  - iMod ("HInvClose" with "[H● Hℓ]") as "_"; first by iExists _; iFrame.
    iModIntro; wp_pures. wp_lam. iApply ("IH" with "[$]").
  - iMod (future_is_completed_from_auth_ra with "H●") as "[H● H◯]".
    iMod ("HInvClose" with "[H● Hℓ]") as "_".
    { iExists (FutureCompleted v). by iFrame "H●". }
    iModIntro; wp_pures. iApply "HΦ". iLeft. iExists _. iSplitR; done.
  - iMod (future_is_cancelled_from_auth_ra with "H●") as "[H● H◯]".
    iMod ("HInvClose" with "[H● Hℓ]") as "_".
    { iExists FutureCancelled. by iFrame "H●". }
    iModIntro; wp_pures. iApply "HΦ". iRight. iSplitR; done.
Qed.

Theorem tryCompleteFuture_spec γ f (v: val):
  is_future γ f -∗
  <<< future_completion_permit γ 1%Qp >>>
    tryCompleteFuture f v @ ⊤ ∖ ↑N
  <<< ∃ (b: bool), if b then future_is_completed γ v
                     else future_is_cancelled γ, RET #b >>>.
Proof.
  iIntros "HFuture" (Φ) "AU". iDestruct "HFuture" as (ℓ ->) "#HFuture".
  wp_lam. wp_pures. wp_bind (CmpXchg _ _ _).
  iInv "HFuture" as (p) "[>H● Hℓ]" "HInvClose".
  iMod "AU" as "[HPermit [_ HClose]]".
  destruct p.
  - wp_cmpxchg_suc.
    iMod (own_update_2 with "H● HPermit") as "[H● HFutureCompleted]".
    {
      apply auth_update with
          (a' := (Some (to_agree (Some v)),
                  permit_auth_ra false, permit_auth_ra true)).
      repeat apply prod_local_update'.
      - by apply alloc_option_local_update.
      - rewrite /permit_auth_ra.
        etransitivity.
        by apply delete_option_local_update, Cinl_exclusive, frac_full_exclusive.
        by apply alloc_option_local_update.
      - done.
    }
    iMod ("HClose" $! true with "HFutureCompleted") as "HΦ".
    iModIntro.
    iMod ("HInvClose" with "[H● Hℓ]") as "_".
    { iExists (FutureCompleted v). iFrame. }
    iModIntro. by wp_pures.
  - iDestruct (own_valid_2 with "H● HPermit")
      as %[[[_ HValid]%pair_included _]%pair_included _]%auth_both_valid.
    exfalso. move: HValid. rewrite /permit_auth_ra.
    rewrite Some_included. case=> HContra.
    * inversion HContra.
    * apply csum_included in HContra.
      destruct HContra as
          [HContra|[(? & ? & ? & HContra & ?)|(? & ? & HContra & ?)]];
        simplify_eq.
  - wp_cmpxchg_fail.
    iMod (future_is_cancelled_from_auth_ra with "H●") as "[H● HFutureCancelled]".
    iMod ("HClose" $! false with "HFutureCancelled") as "HΦ".
    iModIntro.
    iMod ("HInvClose" with "[H● Hℓ]") as "_".
    { iExists FutureCancelled. iFrame. }
    iModIntro. by wp_pures.
Qed.

Theorem tryCancelFuture_spec γ f:
  is_future γ f -∗
  <<< future_cancellation_permit γ 1%Qp >>>
    tryCancelFuture f @ ⊤ ∖ ↑N
  <<< ∃ (b: bool), if b then future_is_cancelled γ
                     else (∃ v, future_is_completed γ v), RET #b >>>.
Proof.
  iIntros "HFuture" (Φ) "AU". iDestruct "HFuture" as (ℓ ->) "#HFuture".
  wp_lam. wp_pures. wp_bind (CmpXchg _ _ _).
  iInv "HFuture" as (p) "[>H● Hℓ]" "HInvClose".
  iMod "AU" as "[HPermit [_ HClose]]".
  destruct p.
  - wp_cmpxchg_suc.
    iMod (own_update_2 with "H● HPermit") as "[H● HFutureCancelled]".
    {
      apply auth_update with
          (a' := (Some (to_agree None),
                  permit_auth_ra true, permit_auth_ra false)).
      repeat apply prod_local_update'.
      - by apply alloc_option_local_update.
      - done.
      - rewrite /permit_auth_ra.
        etransitivity.
        by apply delete_option_local_update, Cinl_exclusive, frac_full_exclusive.
        by apply alloc_option_local_update.
    }
    iMod ("HClose" $! true with "HFutureCancelled") as "HΦ".
    iModIntro.
    iMod ("HInvClose" with "[H● Hℓ]") as "_".
    { iExists FutureCancelled. iFrame. }
    iModIntro. by wp_pures.
  - wp_cmpxchg_fail.
    iMod (future_is_completed_from_auth_ra with "H●") as "[H● HFutureCompleted]".
    iMod ("HClose" $! false with "[HFutureCompleted]") as "HΦ";
      first by iExists _.
    iModIntro.
    iMod ("HInvClose" with "[H● Hℓ]") as "_".
    { iExists (FutureCompleted v). iFrame. }
    iModIntro. by wp_pures.
  - iDestruct (own_valid_2 with "H● HPermit")
      as %[[_ HValid]%pair_included _]%auth_both_valid.
    exfalso. move: HValid. rewrite /permit_auth_ra.
    rewrite Some_included. case=> HContra.
    * inversion HContra.
    * apply csum_included in HContra.
      destruct HContra as
          [HContra|[(? & ? & ? & HContra & ?)|(? & ? & HContra & ?)]];
        simplify_eq.
Qed.

Theorem completeFuture_spec (v: val):
  {{{ True }}}
    completeFuture v
  {{{ γ f, RET f; is_future γ f ∗ future_is_completed γ v ∗
                  future_cancellation_permit γ 1%Qp }}}.
Proof.
  iIntros (Φ) "_ HΦ". wp_lam. wp_pures.
  iMod (own_alloc (future_auth_ra (FutureCompleted v) ⋅
                   (◯ (Some (to_agree (Some v)), permit_state_ra false, None) ⋅
                    ◯ (None, None, Some (Cinl 1%Qp)))))
    as (γ) "[H● [H◯ H◯']]".
  {
    apply auth_both_valid. split; last done.
    repeat (apply prod_included'; split). all: by simpl.
  }
  rewrite -wp_fupd.
  wp_alloc ℓ as "Hℓ".
  iMod (inv_alloc N _ (∃ p, future_invariant γ ℓ p) with "[H● Hℓ]") as "HInv".
  { iExists _; by iFrame. }
  iApply "HΦ". iFrame. iExists _. by iFrame.
Qed.

Theorem emptyFuture_spec:
  {{{ True }}}
    emptyFuture #()
  {{{ γ f, RET f; is_future γ f ∗
                  future_cancellation_permit γ 1%Qp ∗
                  future_completion_permit γ 1%Qp }}}.
Proof.
  iIntros (Φ) "_ HΦ". wp_lam.
  iMod (own_alloc (future_auth_ra FutureEmpty ⋅
                   (◯ (None, Some (Cinl 1%Qp), None) ⋅
                    ◯ (None, None, Some (Cinl 1%Qp)))))
    as (γ) "[H● [H◯ H◯']]".
  {
    apply auth_both_valid. split; last done.
    repeat (apply prod_included'; split). all: by simpl.
  }
  rewrite -wp_fupd.
  wp_alloc ℓ as "Hℓ".
  iMod (inv_alloc N _ (∃ p, future_invariant γ ℓ p) with "[H● Hℓ]") as "HInv".
  { iExists _; by iFrame. }
  iApply "HΦ". iFrame. iExists _. by iFrame.
Qed.

End proof.

Typeclasses Opaque future_completion_permit future_cancellation_permit
            future_is_completed future_is_cancelled future_invariant is_future.
