From iris.heap_lang Require Import notation.

Require Import SegmentQueue.lib.thread_queue.thread_queue.
Require Import SegmentQueue.lib.thread_queue.thread_queue_as_counter.

Section impl.

Variable segment_size : positive.
Variable limit: positive.

Definition new_barrier : val :=
  λ: <>, (ref #0, new_thread_queue segment_size #()).

Definition forRange : val :=
  rec: "loop" "n" "fn" :=
    if: "n" ≤ #0
    then #()
    else "loop" ("n"-#1) "fn" ;; "fn" ("n"-#1).

Definition cancellation_handler : val :=
  rec: "loop" "ctr" "head" "deqIdx" "canceller" <>:=
  let: "arrived" := ! "ctr"
  in if: #(Pos.to_nat limit) ≤ "arrived"
     then #false
     else
       if: CAS "ctr" "arrived" ("arrived" + #1)
       then if: "canceller" #()
            then #()
            else resume segment_size "head" "deqIdx"
              ;;
            #true
       else "loop" "ctr" "head" "deqIdx" "canceller".

Definition await : val :=
  λ: "cancHandle" "threadHandle" "ctr" "tail" "enqIdx" "head" "deqIdx",
  let: "p" := FAA "ctr" #1
  in if: "p" = #(Pos.to_nat limit-1)
     then forRange "p" (λ: "i", resume segment_size "head" "deqIdx") ;; #false
     else suspend segment_size (cancellation_handler "ctr" "head" "deqIdx")
                  "cancHandle" "threadHandle" "tail" "enqIdx".

End impl.

From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import proofmode.
From iris.algebra Require Import auth.
From iris.algebra Require Import list gset excl csum.
From iris.program_logic Require Import atomic.

Require Import SegmentQueue.lib.infinite_array.infinite_array_impl.
Require Import SegmentQueue.lib.infinite_array.iterator.
Require Import SegmentQueue.lib.util.interruptibly.

Section proof.

Context `{!heapG Σ}.

Theorem forRange_spec (Φ: nat -> iProp Σ) (e: val) (n: nat):
  (∀ i, ⌜(i < n)%nat⌝ -∗ {{{ Φ i }}}
                           e #i
                         {{{ v, RET v; Φ (S i) }}})
   -∗
   {{{ Φ O }}}
     forRange #n e
   {{{ v, RET v; Φ n }}}.
Proof.
  iIntros "#HE" (Ψ).
  iInduction n as [|n'] "IH" forall (Ψ); iIntros "!> HΦ0 HΨ"; wp_lam; wp_pures.
  by iApply "HΨ".
  replace #(S n' - 1) with #n'; last by congr (fun x => LitV (LitInt x)); lia.
  wp_bind (forRange _ _).
  wp_apply ("IH" with "[] HΦ0").
  { iIntros "!>" (i HLt). iApply "HE". iPureIntro. lia. }
  iIntros (v) "HΦn".
  wp_pures.
  replace #(S n' - 1) with #n'; last by congr (fun x => LitV (LitInt x)); lia.
  wp_apply ("HE" with "[] HΦn"); last done.
  iPureIntro. lia.
Qed.

Theorem forRange_resource_map (Φ Ψ: nat -> iProp Σ) (e: val):
  (∀ (i: nat), {{{ Φ i }}}
                 e #i
                 {{{ v, RET v; Ψ i }}})
    -∗
  (∀ n, {{{ [∗ list] i ∈ seq 0 n, Φ i }}}
          forRange #n e
        {{{ v, RET v; [∗ list] i ∈ seq 0 n, Ψ i }}}).
Proof.
  iIntros "#HE" (n Ξ) "!> HΦ HΨ".
  iApply (forRange_spec
            (fun j => ([∗ list] i ∈ seq j (n-j), Φ i) ∗
                   ([∗ list] i ∈ seq 0 j, Ψ i))%I
            with "[] [HΦ]").
  - iIntros (i HLt). iIntros "!>" (?) "HPre HPost".
    replace (seq 0 (S i)) with (seq 0 (i + 1)) by (congr (seq 0); lia).
    rewrite seq_add /=.
    destruct (n - i)%nat as [|ni] eqn:X; first by lia.
    simpl.
    iDestruct "HPre" as "[[HΦi HΦ] HΨ]".
    wp_apply ("HE" with "HΦi").
    iIntros (v) "HΨi".
    iApply "HPost".
    replace (n - S i)%nat with ni by lia. iFrame. done.
  - rewrite Nat.sub_0_r. simpl. iFrame.
  - iIntros (v) "!> HH".
    iApply "HΨ".
    iDestruct "HH" as "[_ $]".
Qed.

End proof.

Section barrier_proof.

Variable (limit: positive).

Notation algebra := (authR (optionUR (csumR positiveR positiveR))).

Class barrierG Σ := BarrierG { barrier_inG :> inG Σ algebra }.
Definition barrierΣ : gFunctors := #[GFunctor algebra].
Instance subG_barrierΣ {Σ} : subG barrierΣ Σ -> barrierG Σ.
Proof. solve_inG. Qed.

Context `{iArrayG Σ} `{iteratorG Σ} `{heapG Σ} `{threadQueueG Σ} `{barrierG Σ}
        `{parkingG Σ} `{interruptiblyG Σ}.
Variable (Nth: namespace) (N: namespace).
Variable (namespaces_disjoint : Nth ## N).
Notation iProp := (iProp Σ).

Variable (segment_size: positive).

Definition barrier_entry_piece γ := own γ (◯ (Some (Cinl 1%positive))).
Definition barrier_exit_piece γ := own γ (◯ (Some (Cinr 1%positive))).

Definition is_barrier_inv γ (ℓ: loc)
  (epℓ eℓ dpℓ dℓ: loc) (γa γtq γe γd: gname) (n: nat) :=
  ((if decide (n < Pos.to_nat limit)%nat then own γ (● (Some (Cinl limit))) else
      if decide (n = Pos.to_nat limit) then own γ (● (Some (Cinr limit))) else
        False) ∗
    ℓ ↦ #n ∗ ([∗] replicate (n `mod` Pos.to_nat limit)%nat (barrier_entry_piece γ)) ∗
    thread_queue_as_counter (N .@ "tq") Nth segment_size True (barrier_exit_piece γ)
    γa γtq γe γd eℓ epℓ dℓ dpℓ (n `mod` Pos.to_nat limit)%nat)%I.

Definition is_barrier γ ℓ epℓ eℓ dpℓ dℓ γa γtq γe γd :=
  inv (N .@ "barrier") (∃ n, is_barrier_inv γ ℓ epℓ eℓ dpℓ dℓ γa γtq γe γd n).

Lemma resume_in_barrier_spec γ p epℓ eℓ dpℓ dℓ γa γtq γe γd:
  is_barrier γ p epℓ eℓ dpℓ dℓ γa γtq γe γd -∗
  {{{ awakening_permit γtq }}}
    (resume segment_size) #dpℓ #dℓ
  {{{ RET #(); True }}}.
Proof.
  iIntros "#HBarInv" (Φ) "!> HAwak HΦ". wp_lam. wp_pures.
  awp_apply (try_deque_thread_as_counter_spec (N .@ "tq") with "HAwak") without "HΦ".
  iInv "HBarInv" as (?) "(HAuth & Hl & HPieces & HTq)".
  iAaccIntro with "HTq".
  {
    iIntros "HTq !>".
    iSplitL; last done.
    iExists _. iFrame.
  }
  iIntros (?) "(_ & HTq & HState)".
  iDestruct "HState" as "[->|HState]".
  {
    iSplitL; first by iExists _; iFrame.
    iIntros "!> HΦ". wp_pures. by iApply "HΦ".
  }

  iDestruct "HState" as (? ? ?) "(-> & #[HIsThread HThreadLocs] &
    [[HResTok #HRendRes]|HNoPerms])".
  2: {
    iSplitR "HNoPerms".
    by iExists _; iFrame.
    iIntros "!> HΦ". wp_pures.
    awp_apply (unpark_spec with "HIsThread") without "HΦ".
    iAaccIntro with "HNoPerms".
    by iIntros ">HNoPerms !>".
    iIntros "HPerms !> HΦ". wp_pures. by iApply "HΦ".
  }
  {
    iSplitR "HResTok"; first by iExists _; iFrame.
    iIntros "!> HΦ". wp_pures.

    awp_apply (thread_queue_as_counter_unpark_spec with
                   "HRendRes HIsThread HThreadLocs") without "HΦ".
    iInv "HBarInv" as (?) "(HAuth & Hl & HPieces & HTq)".
    iCombine "HResTok" "HTq" as "HAacc".
    iAaccIntro with "HAacc".
    { iIntros "[$ HTq]". iExists _. by iFrame. }
    iIntros "HTq". iSplitL.
    by iExists _; iFrame.
    iIntros "!> HΦ". wp_pures. by iApply "HΦ".
  }
Qed.

Lemma ucmra_cancel_local_update {A: ucmraT} (x: A) `{!Cancelable x}:
  (x, x) ~l~> (ε, ε).
Proof.
  intros n f ? Heq. split; first by apply ucmra_unit_validN.
  apply (cancelableN x); rewrite /= ucmra_unit_right_id; first done.
  destruct f as [f'|]; simpl in *.
  by rewrite ucmra_unit_left_id.
  by rewrite ucmra_unit_right_id.
Qed.

Lemma await_spec Nint γi cancHandle γth (threadHandle: loc)
      γ p epℓ eℓ dpℓ dℓ γa γtq γe γd:
  is_interrupt_handle Nint γi cancHandle -∗
  is_thread_handle Nth γth #threadHandle -∗
  is_barrier γ p epℓ eℓ dpℓ dℓ γa γtq γe γd -∗
  {{{ thread_doesnt_have_permits γth ∗ barrier_entry_piece γ }}}
  (await segment_size limit) cancHandle #threadHandle #p #epℓ #eℓ #dpℓ #dℓ
  {{{ (v: bool), RET #v;
      ⌜v = false⌝ ∧ thread_doesnt_have_permits γth ∗ barrier_exit_piece γ ∨
      ⌜v = true⌝ ∧ interrupted γi }}}.

Proof.
  iIntros "#HIntHandle #HThreadHandle #HBarInv" (Φ) "!> [HNoPerms HEnt] HΦ".

  wp_lam. wp_pures. wp_bind (FAA _ _).
  iInv "HBarInv" as (n) "(HAuth & Hℓ & HEntries & HTq)" "HClose".
  destruct (decide (n < Pos.to_nat limit)%nat).
  2: {
    destruct (decide (n = Pos.to_nat limit)); last by iDestruct "HAuth" as ">[]".
    iDestruct "HAuth" as ">HAuth".
    iDestruct (own_valid_2 with "HAuth HEnt") as %[HH _]%auth_both_valid.
    exfalso.

    move: HH. rewrite Some_included. case. by intros; simplify_eq.
    rewrite csum_included. case; first done. case.
    by intros (? & ? & _ & HH & _); simplify_eq.
    by intros (? & ? & HH & _); simplify_eq.
  }

  wp_faa.
  replace (n + 1) with (Z.of_nat (S n)) by lia.
  destruct (decide (n = Pos.to_nat limit - 1)%nat).
  {
    replace (n `mod` Pos.to_nat limit)%nat with (n);
      last by symmetry; rewrite Nat.mod_small_iff; lia.
    subst.
    replace (S (_ - _)) with (Pos.to_nat limit) by lia.
    rewrite /barrier_entry_piece.
    iAssert (own γ (◯ Some (Cinl limit))) with "[HEnt HEntries]" as "HFrag".
    {
      clear.
      remember (Pos.to_nat limit) as limN.
      replace limit with (Pos.of_nat limN) by (subst; apply Pos2Nat.id).
      assert (limN > 0)%nat as HNonZero by lia.
      clear HeqlimN.
      iInduction limN as [|limN'] "IH" forall (HNonZero); simpl in *. lia.
      inversion HNonZero; first done. subst.
      destruct limN'; first by lia.
      rewrite /= Nat.sub_0_r.
      iDestruct "HEntries" as "[HEnt' HRepl]".
      iSpecialize ("IH" with "[%] HEnt' HRepl"); first lia.
      replace (Pos.of_nat (S (S limN'))) with
          (Pos.of_nat 1%nat + Pos.of_nat (S limN'))%positive
        by rewrite -Nat2Pos.inj_add //.
      rewrite Cinl_op Some_op auth_frag_op own_op. iFrame.
    }
    iMod (own_update_2 with "HAuth HFrag") as "HAuth".
    { apply auth_update_dealloc, ucmra_cancel_local_update, _. }
    iMod (own_update with "HAuth") as "[HAuth HFrag]".
    by apply auth_update_alloc, (alloc_option_local_update (Cinr limit)).
    iAssert ([∗] replicate (Pos.to_nat limit) (barrier_exit_piece γ))%I
      with "[HFrag]" as "HExit".
    {
      clear.
      remember (Pos.to_nat limit) as limN.
      replace limit with (Pos.of_nat limN) by (subst; apply Pos2Nat.id).
      assert (limN > 0)%nat as HNonZero by lia.
      clear HeqlimN.
      iInduction limN as [|limN'] "IH" forall (HNonZero); simpl in *. lia.
      inversion HNonZero; subst; first by iFrame.
      replace (Pos.of_nat (S limN')) with
          (Pos.of_nat 1%nat + Pos.of_nat limN')%positive;
        last by rewrite -Nat2Pos.inj_add //; lia.
      rewrite Cinr_op Some_op auth_frag_op own_op.
      iDestruct "HFrag" as "[$ HFrag]".
      iApply ("IH" with "[%] [$]").
      lia.
    }
    (* TODO: dequeue (limit - 1) threads. *)
    remember (Pos.to_nat limit - 1)%nat as sleepers.
    replace (Pos.to_nat limit) with (S sleepers) by lia.
    simpl. iDestruct "HExit" as "[HMyExit HWakers]".
    iAssert (|==> thread_queue_as_counter (N.@"tq") Nth segment_size True
                  (barrier_exit_piece γ) γa γtq γe γd eℓ epℓ dℓ dpℓ O
                  ∗ [∗] replicate sleepers (awakening_permit γtq))%I
      with "[HTq HWakers]" as ">[HTq HAwaken]".
    {
      iClear "HIntHandle HThreadHandle HBarInv". clear.
      iInduction (sleepers) as [|sleepers] "IH"; simpl.
      by iFrame.
      iDestruct "HWakers" as "[HWaker HWakers]".
      iMod (thread_as_counter_register_for_dequeue with "HWaker HTq")
        as "[$ HTq]"; first by lia.
      rewrite /= Nat.sub_0_r.
      iApply ("IH" with "HTq HWakers").
    }
    iMod ("HClose" with "[Hℓ HTq HAuth]") as "_".
    {
      subst.
      replace (S (Pos.to_nat limit - 1)%nat) with (Pos.to_nat limit) by lia.
      iExists _. iFrame "Hℓ".
      rewrite decide_False; last lia. rewrite decide_True; last lia.
      iFrame "HAuth".
      rewrite Nat.mod_same /=; last lia.
      iFrame.
    }
    iModIntro.
    wp_pures.
    rewrite bool_decide_eq_true_2; last by congr (fun x => LitV (LitInt x)); lia.
    wp_pures.
    wp_apply (forRange_resource_map
                (fun _ => awakening_permit γtq) (fun _ => True)%I
             with "[] [HAwaken]").
    - iIntros (i Ψ) "!> HAwak HPost". wp_pures.
      wp_apply (resume_in_barrier_spec with "[$] HAwak").
      iIntros (_). by iApply "HPost".
    - remember O as n. clear.
      iInduction sleepers as [|sleepers] "IH" forall (n); first done. simpl.
      iDestruct "HAwaken" as "[$ HAwaken]".
      iApply ("IH" with "HAwaken").
    - iIntros (v) "_". wp_pures.
      iApply "HΦ". iLeft. by iFrame.
  }
  {
    iMod (thread_queue_as_counter_append with "[] HTq") as "[HSusp HTq]";
      first done.
    iMod ("HClose" with "[-HΦ HSusp HNoPerms]") as "_".
    {
      iExists (S n). iFrame "Hℓ".
      destruct (decide (S n < Pos.to_nat limit)%nat); try lia.
      iFrame "HAuth".
      replace (S n `mod` Pos.to_nat limit)%nat with (S n);
        last by symmetry; rewrite Nat.mod_small_iff; lia.
      replace (n `mod` Pos.to_nat limit)%nat with (n);
        last by symmetry; rewrite Nat.mod_small_iff; lia.
      simpl. iFrame.
    }
    iIntros "!>". wp_pures.
    rewrite bool_decide_eq_false_2.
    2: intros HContra; inversion HContra; lia.
    wp_pures.

    wp_lam. wp_pures. wp_lam. wp_pures.
    awp_apply (try_enque_thread_as_counter_spec (N.@"tq") with
                   "HThreadHandle HSusp HNoPerms") without "HΦ".

    iInv "HBarInv" as (n') "(HAuth & Hℓ & HEntries & HTq)".
    iAaccIntro with "HTq".
    { iIntros "HTq !>". iSplitL; last done. iExists _. iFrame. }
    iIntros (v) "[HTq HStates]".
    iIntros "!>".
    iSplitR "HStates".
    { iExists _. iFrame. }
    iIntros "HΦ".

    iDestruct "HStates" as "[HPures|(-> & HR & HNoPerms)]".
    2: { wp_pures. iApply "HΦ". iLeft. by iFrame. }
    iDestruct "HPures" as (i s ->) "(#HSegLoc & #HRend & HInhToken)".
    wp_pures. wp_lam. wp_pures.
    wp_apply (interruptibly_spec _ (inhabitant_token γtq i)
                                   (fun _ => thread_has_permit γth ∗ barrier_exit_piece γ)%I
                                   (fun _ => interrupted γi)
              with "[HInhToken]").

Abort.

End barrier_proof.
