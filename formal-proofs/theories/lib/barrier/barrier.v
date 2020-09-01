Require Import SegmentQueue.lib.thread_queue.thread_queue.
Require Import SegmentQueue.lib.thread_queue.thread_queue_as_counter.

From iris.heap_lang Require Import notation.

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
     then InjRV #()
     else
       if: CAS "ctr" "arrived" ("arrived" - #1)
       then if: "canceller" #()
            then InjLV #()
            else resume segment_size "head" "deqIdx"
              ;;
            InjLV #()
       else "loop" "ctr" "head" "deqIdx" "canceller" #().

Definition await : val :=
  λ: "cancHandle" "threadHandle" "ctr" "tail" "enqIdx" "head" "deqIdx",
  let: "p" := FAA "ctr" #1
  in if: "p" = #(Pos.to_nat limit-1)
     then forRange "p" (λ: "i", resume segment_size "head" "deqIdx") ;; InjRV #()
     else suspend segment_size (cancellation_handler "ctr" "head" "deqIdx")
                  "cancHandle" "threadHandle" "tail" "enqIdx".

End impl.

Require Import SegmentQueue.lib.infinite_array.infinite_array_impl.
Require Import SegmentQueue.lib.infinite_array.iterator.
Require Import SegmentQueue.lib.util.interruptibly.
From SegmentQueue.util Require Import everything local_updates.

From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import auth.
From iris.algebra Require Import list gset excl csum numbers.
From iris.program_logic Require Import atomic.
From iris.heap_lang Require Import proofmode.

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

Notation algebra := (authR (prodUR natUR
                                   (optionUR (csumR positiveR positiveR)))).

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

Definition barrier_entry_piece γ := own γ (◯ (ε, Some (Cinl 1%positive))).
Definition barrier_exit_piece γ := own γ (◯ (ε, Some (Cinr 1%positive))).

Definition is_barrier_inv γ (ℓ: loc)
  (epℓ eℓ dpℓ dℓ: loc) (γa γtq γe γd: gname) (n: nat) :=
  ((if decide (n < Pos.to_nat limit)%nat then own γ (● (n, Some (Cinl limit))) else
      if decide (n = Pos.to_nat limit) then own γ (● (n, Some (Cinr limit))) else
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

Lemma await_spec Nint γi cancHandle γth (threadHandle: loc)
      γ p epℓ eℓ dpℓ dℓ γa γtq γe γd:
  is_interrupt_handle Nint γi cancHandle -∗
  is_thread_handle Nth γth #threadHandle -∗
  is_barrier γ p epℓ eℓ dpℓ dℓ γa γtq γe γd -∗
  {{{ thread_doesnt_have_permits γth ∗ barrier_entry_piece γ }}}
  (await segment_size limit) cancHandle #threadHandle #p #epℓ #eℓ #dpℓ #dℓ
  {{{ (v: val), RET v;
      ⌜v = InjRV #()⌝ ∧ (thread_doesnt_have_permits γth ∨ interrupted γi) ∗
                          barrier_exit_piece γ ∨
      ⌜v = InjLV #()⌝ ∧ interrupted γi ∗ barrier_entry_piece γ }}}.
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

    move: HH. rewrite prod_included. rewrite Some_included.
    case. intros _. case. by intros; simplify_eq.
    rewrite csum_included. case; first done. case.
    by intros (? & ? & _ & HH & _); simplify_eq.
    by intros (? & ? & HH & _); simplify_eq.
  }

  wp_faa.
  replace (n + 1)%Z with (Z.of_nat (S n)) by lia.
  destruct (decide (n = Pos.to_nat limit - 1)%nat).
  {
    replace (n `mod` Pos.to_nat limit)%nat with (n);
      last by symmetry; rewrite Nat.mod_small_iff; lia.
    subst.
    replace (S (_ - _)) with (Pos.to_nat limit) by lia.
    rewrite /barrier_entry_piece.
    iAssert (own γ (◯ (ε, Some (Cinl limit)))) with "[HEnt HEntries]" as "HFrag".
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
      rewrite Cinl_op Some_op pair_op_2 auth_frag_op own_op. iFrame.
    }
    iMod (own_update_2 with "HAuth HFrag") as "HAuth".
    { apply auth_update_dealloc, prod_local_update_2, ucmra_cancel_local_update, _. }
    iMod (own_update with "HAuth") as "[HAuth HFrag]".
    { apply auth_update_alloc, prod_local_update'; simpl.
      - apply (nat_local_update _ 0 (Pos.to_nat limit) 1). lia.
      - by apply (alloc_option_local_update (Cinr limit)).
    }
    iAssert (own γ (◯ (ε, Some (Cinr limit))) ∗
             own γ (◯ (1%nat, ε)))%I with "[HFrag]" as "[HFrag HInhabit]".
    by rewrite -own_op -auth_frag_op -pair_op.
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
      rewrite Cinr_op Some_op pair_op_2 auth_frag_op own_op.
      iDestruct "HFrag" as "[$ HFrag]".
      iApply ("IH" with "[%] [$]").
      lia.
    }
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
    iMod (own_update with "HAuth") as "[HAuth HFrag]".
    { apply auth_update_alloc, prod_local_update_1, (nat_local_update _ 0 (S n) 1).
      lia. }
    iMod ("HClose" with "[-HΦ HSusp HNoPerms HFrag]") as "_".
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
                   "HThreadHandle HSusp HNoPerms") without "HΦ HFrag".

    iInv "HBarInv" as (n') "(HAuth & Hℓ & HEntries & HTq)".
    iAaccIntro with "HTq".
    { iIntros "HTq !>". iSplitL; last done. iExists _. iFrame. }
    iIntros (v) "[HTq HStates]".
    iIntros "!>".
    iSplitR "HStates".
    { iExists _. iFrame. }
    iIntros "[HΦ HFrag]".

    iDestruct "HStates" as "[HPures|(-> & HR & HNoPerms)]".
    2: { wp_pures. iApply "HΦ". iLeft. by iFrame. }
    iDestruct "HPures" as (i s ->) "(#HSegLoc & #HRend & HInhToken)".
    wp_pures. wp_lam. wp_pures.
    wp_apply (interruptibly_spec _ (inhabitant_token γtq i ∗ own γ (◯ (1%nat, ε)))%I
                                 (fun v => ⌜v = #()⌝ ∧ (thread_doesnt_have_permits γth
                                                     ∨ interrupted γi) ∗
                                                    barrier_exit_piece γ)%I
                                 (fun v => ⌜v = #()⌝ ∧ interrupted γi ∗ barrier_entry_piece γ)%I
              with "[HInhToken HFrag]").
    {
      iFrame "HIntHandle HInhToken HFrag".
      iSplit.
      {
        iIntros (Φ') "!> [HInhTok HFrag] HΦ'". wp_pures. wp_bind (!_)%E.
        rewrite /is_thread_handle.
        awp_apply (thread_queue_as_counter_check_thread_permits_spec with
                      "HThreadHandle HSegLoc HRend") without "HΦ' HFrag".
        iInv "HBarInv" as (?) "(HAuth & Hℓ & HEntries & HTq)".
        iCombine "HInhTok" "HTq" as "HAacc".
        iAaccIntro with "HAacc".
        { iIntros "[$ HTq]". by iExists _; iFrame. }
        iIntros (b) "[HTq HRes] !>".
        iSplitR "HRes".
        by iExists _; iFrame.
        iIntros "[HΦ HFrag]".
        iDestruct "HRes" as "[[-> HInh]|(-> & HPerm & HR)]".
        all: wp_pures.
        - iApply "HΦ".
          iLeft; by iFrame.
        - iAssert (▷ thread_has_permit γth)%I with "[$]" as "HHasPerm".
          awp_apply (thread_update_state _ _ _ true with "HThreadHandle") without "HΦ HR".
          iAaccIntro with "HHasPerm".
          by iIntros "$ //".
          iIntros "HNoPerms !> [HΦ HR]".
          wp_pures. iApply "HΦ".
          iRight; iFrame. by iExists _.
      }
      iIntros (Φ') "!> [[HInhToken HFrag] #HInterrupted] HΦ'". wp_pures.
      iClear "HIntHandle".
      move: namespaces_disjoint. clear. intros.
      iLöb as "IH". wp_bind (!_)%E.

      iInv "HBarInv" as (n) "(HAuth & Hℓ & HEntries & HTq)" "HClose".
      destruct (decide (n < Pos.to_nat limit)%nat).
      2: {
        destruct (decide (n = Pos.to_nat limit));
          last by iDestruct "HAuth" as ">[]".
        wp_load.
        subst. rewrite Nat.mod_same; last lia.
        iMod (thread_queue_abandon_if_empty with "HInhToken HTq")
          as "(HTq & HExit & #HReason)".
        iMod ("HClose" with "[HAuth Hℓ HEntries HTq]") as "_".
        { iExists _; iFrame "Hℓ".
          rewrite decide_False // decide_True // Nat.mod_same; last lia.
          iFrame. }
        iModIntro. wp_pures.
        rewrite bool_decide_eq_true_2; last done. wp_pures.
        iApply "HΦ'". iRight. iFrame.
        repeat iSplitR; try done. by iRight.
      }
      wp_load.
      iMod ("HClose" with "[HAuth Hℓ HEntries HTq]") as "_".
      { iExists _; iFrame "Hℓ". rewrite decide_True //. iFrame. }

      iModIntro. wp_pures. rewrite bool_decide_eq_false_2; last lia.
      wp_pures.
      wp_bind (CmpXchg _ _ _).
      iInv "HBarInv" as (n') "(HAuth & Hℓ & HEntries & HTq)" "HClose".
      destruct (decide (n = n')).
      2: {
        wp_cmpxchg_fail; first by intro HContra; simplify_eq.
        iMod ("HClose" with "[HAuth Hℓ HEntries HTq]") as "_".
        by iExists _; iFrame.
        iModIntro. wp_pures. wp_lam. wp_pures.
        by iApply ("IH" with "HInhToken HFrag HΦ'").
      }
      subst.
      rewrite decide_True; last done.
      iDestruct "HAuth" as ">HAuth".
      iAssert (⌜(n' > 0)%nat⌝)%I with "[-]" as %HN'Gt.
      {
        iDestruct (own_valid_2 with "HAuth HFrag") as
            %[[HOk%nat_included _]%prod_included _]%auth_both_valid.
        iPureIntro; simpl in *; lia.
      }
      iMod (do_cancel_rendezvous_as_counter_spec with "HInhToken HTq")
           as "[HTq HRes]".
      by rewrite Nat.mod_small; lia.
      iMod (own_update_2 with "HAuth HFrag") as "HAuth".
      {
        apply auth_update_dealloc, prod_local_update_1,
          (nat_local_update _ 1 (n'-1) 0).
        lia.
      }
      wp_cmpxchg_suc.
      replace  (n' `mod` Pos.to_nat limit)%nat with n';
        last by symmetry; apply Nat.mod_small; lia.
      destruct n' as [|n']; first by lia.
      simpl.
      iDestruct "HEntries" as "[HEntry HEntries]".
      iMod ("HClose" with "[HAuth Hℓ HEntries HTq]") as "_".
      {
        iExists n'. rewrite /is_barrier_inv.
        replace  (n' `mod` Pos.to_nat limit)%nat with n';
          last by symmetry; apply Nat.mod_small; lia.
        rewrite Nat.sub_0_r decide_True; last lia.
        iFrame "HEntries HTq HAuth".
        replace (S n' - 1)%Z with (Z.of_nat n') by lia.
        iFrame.
      }
      iModIntro. wp_pures.

      iDestruct "HRes" as "[[HCancTok #HRendCanc]|(HArr & HAwak & #HRendRes)]".
      2: {
        iDestruct "HArr" as (?) "[#HArrMapsto Hℓ]".
        wp_lam. wp_lam. wp_pures.

        awp_apply (segment_data_at_spec) without "HΦ' HEntry Hℓ HAwak".
        by iPureIntro; apply Nat.mod_upper_bound; lia.
        iInv "HBarInv" as (?) "(HAuth & Hl & HPieces & HTq)".
        iDestruct "HTq" as (? ?) "[(HInfArr & HTail') HTail'']".
        iDestruct (is_segment_by_location with "HSegLoc HInfArr")
          as (? ?) "[HIsSeg HInfArrRestore]".
        iAaccIntro with "HIsSeg".
        {
          iIntros "HIsSeg".
          iDestruct ("HInfArrRestore" with "HIsSeg") as "HInfArr".
          iIntros "!>". iSplitL; last done.
          iExists _. iFrame. iExists _, _. iFrame.
        }
        iIntros (?) "(HIsSeg & #HArrMapsto' & #HCellInv)".
        iDestruct (bi.later_wand with "HInfArrRestore HIsSeg") as "HInfArr".
        iSplitL; first by iExists _; iFrame; iExists _, _; iFrame.
        iIntros "!> (HΦ' & HEntry & Hℓ & HAwak)". wp_pures.
        iDestruct (array_mapsto'_agree with "HArrMapsto HArrMapsto'") as %->.
        iAssert (▷ _ ↦ RESUMEDV)%I with "Hℓ" as "Hℓ".
        awp_apply getAndSet.getAndSet_spec without "HΦ' HEntry HAwak".
        iAssert (▷ _ ↦ RESUMEDV ∧ ⌜val_is_unboxed RESUMEDV⌝)%I
          with "[Hℓ]" as "HAacc".
        by iFrame.
        iAaccIntro with "HAacc"; first by iIntros "[$ _] //".
        iIntros "Hℓ !> (HΦ' & HEntry & HAwak)".
        wp_pures.
        wp_apply (resume_in_barrier_spec with "[$] [$]"). iIntros (_).
        wp_pures.
        iApply "HΦ'".
        iLeft. iFrame "HEntry HInterrupted". done.
      }
      awp_apply (cancel_cell_spec with "HRendCanc HSegLoc HCancTok")
        without "HΦ' HEntry".
      iInv "HBarInv" as (?) "(HAuth & Hl & HPieces & HTq)".
      iDestruct "HTq" as (? ?) "[HTq HTail'']".
      iAaccIntro with "HTq".
      { iIntros "HTq !>". iSplitL; last done. iExists _. iFrame.
        iExists _, _. iFrame. }
      iIntros (b) "[HTq HAwak]".
      iSplitR "HAwak".
      { iExists _. iFrame. iExists _, _. iFrame. done. }
      iIntros "!> [HΦ' HEntryPiece]".
      iDestruct "HAwak" as "[[-> HAwak]|->]"; wp_pures.
      wp_apply (resume_in_barrier_spec with "[$] [$]"); iIntros (_); wp_pures.
      all: by iApply "HΦ'"; iLeft; iFrame "HInterrupted HEntryPiece".
    }
    iIntros (? ?) "HOk".
    iDestruct "HOk" as "[(-> & -> & HInt & HEnt)|(-> & -> & HInt & HExit)]".
    - iApply "HΦ". iRight. by iFrame.
    - iApply "HΦ". iLeft. by iFrame.
  }
Qed.

Lemma new_barrier_spec:
  {{{ True }}}
    new_barrier segment_size #()
  {{{ p γ γa γtq γe γd eℓ epℓ dℓ dpℓ, RET (#p, ((#epℓ, #eℓ), (#dpℓ, #dℓ)));
      is_barrier γ p epℓ eℓ dpℓ dℓ γa γtq γe γd ∗
      [∗] replicate (Pos.to_nat limit) (barrier_entry_piece γ)
  }}}.
Proof.
  iIntros (Φ) "_ HΦ".
  wp_lam.
  iMod (own_alloc (● (O, Some (Cinl limit)) ⋅ ◯ (O, Some (Cinl limit))))
    as (γ) "[HAuth HFrag]".
  by apply auth_both_valid; split; done.
  wp_apply new_thread_queue_spec; first done.
  iIntros (γa γtq γe γd eℓ epℓ dℓ dpℓ) "HTq".
  wp_bind (ref _)%E.
  rewrite -wp_fupd.
  wp_alloc p as "Hp".
  iMod (inv_alloc (N .@ "barrier") _
                  (∃ n, is_barrier_inv γ p epℓ eℓ dpℓ dℓ γa γtq γe γd n)%I
          with "[-HΦ HFrag]") as "#HInv".
  {
    iExists O. rewrite /is_barrier_inv. rewrite decide_True; last lia.
    iFrame "HAuth". iFrame "Hp". rewrite Nat.mod_small; last lia. simpl.
    iSplitR; first done. iExists [], O. by iFrame.
  }
  iModIntro. wp_pures.
  iApply "HΦ".
  iFrame "HInv".
  iClear "HInv". clear.

  remember (Pos.to_nat limit) as NLim.
  replace limit with (Pos.of_nat NLim) by (subst; apply Pos2Nat.id).
  assert (NLim > 0)%nat as HGt by (subst; lia). move: HGt. clear.
  intros HGt.
  iInduction (NLim) as [|NLim] "IH"; first done.
  simpl.
  inversion HGt; subst; first by iFrame.
  replace (Pos.of_nat (S NLim)) with (1 + Pos.of_nat NLim)%positive;
    last by rewrite Nat2Pos.inj_succ; lia.
  rewrite Cinl_op Some_op pair_op_2 auth_frag_op own_op.
  iDestruct "HFrag" as "[$ HFrag]".
  iApply ("IH" with "[%] [$]").
  lia.
Qed.

End barrier_proof.
