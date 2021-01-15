Require Import SegmentQueue.lib.thread_queue.thread_queue.
From SegmentQueue.lib.concurrent_linked_list.infinite_array
     Require Import array_spec iterator.iterator_impl.
Require Import SegmentQueue.lib.util.future.
Require Import SegmentQueue.lib.util.forRange.
From iris.heap_lang Require Import notation.

Section impl.

Variable array_interface: infiniteArrayInterface.
Variable limit: positive.

Definition newBarrier: val :=
  λ: <>, (ref #0, newThreadQueue array_interface #()).

Definition barrierResume: val :=
  λ: "d", resume array_interface #(Z.of_nat 300) #true #false #false "d"
                 (λ: <>, #()) #().

Definition await : val :=
  λ: "barrier",
  let: "counter" := Fst "barrier" in
  let: "e" := Fst (Snd "barrier") in
  let: "d" := Snd (Snd "barrier") in
  let: "p" := FAA "counter" #1
  in if: "p" = #(Pos.to_nat limit-1)
     then forRange "p" (λ: <>, barrierResume "d") ;; fillThreadQueueFuture #()
     else match: suspend array_interface "e" with
            InjR "v" => "v"
          | InjL "x" => "undefined"
          end.

Definition cancelBarrierFuture : val :=
  λ: "barrier" "f",
  let: "counter" := Fst "barrier" in
  let: "onCancellation" :=
     rec: "loop" <> :=
       let: "c" := !"counter" in
       if: "c" = #(Pos.to_nat limit) then #false
       else if: CAS "counter" "c" ("c" - #1) then #true
            else "loop" #()
  in
  let: "d" := Snd (Snd "barrier") in
  tryCancelThreadQueueFuture' array_interface
                              #false #(Z.of_nat 300) #false #false
                              "d" "onCancellation"
                              (λ: <>, #()) (λ: <>, #()) "f".

End impl.

From SegmentQueue.util Require Import everything big_opL local_updates.
From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import numbers auth list gset excl csum.
From iris.program_logic Require Import atomic.
From iris.heap_lang Require Import proofmode.

Section proof.

Notation algebra := (authR (prodUR natUR
                                   (optionUR (csumR positiveR positiveR)))).

Class barrierG Σ := BarrierG { barrier_inG :> inG Σ algebra }.
Definition barrierΣ : gFunctors := #[GFunctor algebra].
Instance subG_barrierΣ {Σ} : subG barrierΣ Σ -> barrierG Σ.
Proof. solve_inG. Qed.

Context `{heapG Σ} `{iteratorG Σ} `{threadQueueG Σ} `{futureG Σ} `{barrierG Σ}.
Variable (limit: positive).
Variable (N NFuture: namespace).
Variable (HNDisj: N ## NFuture).
Let NBar := N .@ "Barrier".
Let NTq := N .@ "Tq".
Notation iProp := (iProp Σ).

Definition barrier_entry_piece γ := own γ (◯ (ε, Some (Cinl 1%positive))).
Definition barrier_exit_piece γ := own γ (◯ (ε, Some (Cinr 1%positive))).
Definition barrier_inhabitant_permit γ := own γ (◯ (1, ε)).

Definition barrier_inv (γb γtq: gname) (ℓ: loc) (n: nat): iProp :=
  (⌜n < Pos.to_nat limit⌝ ∧ own γb (● (n, Some (Cinl limit))) ∨
   ⌜n = Pos.to_nat limit⌝ ∧ own γb (● (n, Some (Cinr limit))))
  ∗ ℓ ↦ #n ∗ [∗] replicate (n `mod` Pos.to_nat limit) (barrier_entry_piece γb)
  ∗ thread_queue_state γtq (n `mod` Pos.to_nat limit).

Variable array_interface: infiniteArrayInterface.
Variable array_spec: infiniteArraySpec _ array_interface.

Let tqParams γb :=
  @ThreadQueueParameters Σ false True (barrier_exit_piece γb) True
                         (fun v => ⌜#v = #()⌝)%I False.

Let isThreadQueue γb := is_thread_queue NTq NFuture (tqParams γb) _ array_spec.

Definition is_barrier_future γb :=
  is_thread_queue_future NTq NFuture (tqParams γb) _ array_spec.

Definition is_barrier γb γa γtq γe γd (s: val): iProp :=
  ∃ e d (p: loc), ⌜s = (#p, (e, d))%V⌝ ∧
  inv NBar (∃ n, barrier_inv γb γtq p n)
  ∗ isThreadQueue γb γa γtq γe γd e d.

Theorem newBarrier_spec:
  {{{ inv_heap_inv }}}
    newBarrier array_interface #()
  {{{ γb γa γtq γe γd s, RET s; is_barrier γb γa γtq γe γd s
    ∗ [∗] replicate (Pos.to_nat limit) (barrier_entry_piece γb) }}}.
Proof.
  iIntros (Φ) "#HHeap HΦ".
  iMod (own_alloc (● (0, Some (Cinl limit)) ⋅ ◯ (0, Some (Cinl limit))))
    as (γb) "[H● H◯]"; first by apply auth_both_valid.
  wp_lam. wp_bind (newThreadQueue _ _).
  iApply (newThreadQueue_spec with "HHeap").
  iIntros (γa γtq γe γd e d) "!> [#HTq HThreadState]".
  rewrite -wp_fupd. wp_alloc p as "Hp". wp_pures.
  iMod (inv_alloc NBar _ (∃ n, barrier_inv γb γtq p n) with "[-HΦ H◯]")
    as "#HInv".
  { iExists 0. iFrame "Hp". rewrite Nat.mod_0_l; last lia. simpl.
    iFrame "HThreadState". iLeft. iFrame. iPureIntro. lia. }
  iApply "HΦ". iSplitR.
  { iExists _, _, _. iSplitR; first done. by iFrame "HInv HTq". }
  rewrite big_opL_replicate_irrelevant_element -big_opL_own.
  2: { destruct (Pos.to_nat limit) eqn:E. lia. done. }
  remember (Pos.to_nat limit) as NLim.
  replace limit with (Pos.of_nat NLim) by (subst; apply Pos2Nat.id).
  assert (NLim > 0)%nat as HGt by (subst; lia). move: HGt. clear.
  intros HGt.
  iInduction (NLim) as [|NLim] "IH"; first lia.
  simpl.
  inversion HGt; subst; first by iFrame.
  replace (Pos.of_nat (S NLim)) with (1 + Pos.of_nat NLim)%positive;
    last by rewrite Nat2Pos.inj_succ; lia.
  rewrite Cinl_op Some_op pair_op_2 auth_frag_op own_op.
  move: (big_opL_op_prodR 0)=> /= HBigOpL.
  rewrite -big_opL_auth_frag !HBigOpL !big_opL_op_ucmra_unit.
  rewrite own_op. iDestruct "H◯" as "[$ HFrag]".
  iApply ("IH" with "[//] HFrag").
Qed.

Lemma resumeBarrier_spec R maxWait (wait: bool) γa γtq γe γd e d:
  {{{ isThreadQueue R γa γtq γe γd e d ∗ awakening_permit γtq }}}
    resume array_interface #(Z.of_nat maxWait) #true #false #wait d (λ: <>, #())%V #()
  {{{ RET #true; True }}}.
Proof.
  iIntros (Φ) "[#HTq HAwak] HΦ".
  iApply (resume_spec with "[] [HAwak]").
  5: { by iFrame "HTq HAwak". }
  by solve_ndisj. done. done.
  { simpl. iIntros (Ψ) "!> _ HΨ". wp_pures. by iApply "HΨ". }
  iIntros "!>" (r) "Hr". simpl. destruct r; first by iApply "HΦ".
  iDestruct "Hr" as "[% _]"; lia.
Qed.

Lemma await_spec γb γa γtq γe γd s:
  {{{ is_barrier γb γa γtq γe γd s ∗ barrier_entry_piece γb }}}
    await array_interface limit s
  {{{ γf v, RET v; is_barrier_future γb γtq γa γf v ∗
                   thread_queue_future_cancellation_permit γf ∗
                   barrier_inhabitant_permit γb }}}.
Proof.
  iIntros (Φ) "[#HBarrier HEntry] HΦ". wp_lam.
  iDestruct "HBarrier" as (e d p ->) "[HInv HTq]". wp_pures.
  wp_bind (FAA _ _).
  iInv "HInv" as (n) "(>[[% H●]|[-> HContra]] & Hℓ & HEntries & HState)".
  2: {
    iDestruct (own_valid_2 with "HContra HEntry") as
        %[[_ HInc]%prod_included _]%auth_both_valid. exfalso.
    move: HInc=> /=. rewrite Some_included. case.
    + intros HContra. inversion HContra.
    + rewrite csum_included. case; first done.
      case; by intros (? & ? & ? & ? & ?).
  }
  iCombine "HEntry" "HEntries" as "HEntries".
  rewrite Nat.mod_small; last lia.
  destruct (decide (n = Pos.to_nat limit - 1)) as [->|HLt].
  - wp_faa.
    iAssert ([∗] replicate (Pos.to_nat limit) (barrier_entry_piece γb))%I
            with "[HEntries]" as "HEntries".
    { iEval (replace (Pos.to_nat limit) with (1 + (Pos.to_nat limit - 1))
              by lia). iFrame. }
    iAssert (own γb (◯ (0, Some (Cinl limit)))) with "[HEntries]" as "H◯".
    {
      clear. remember (Pos.to_nat limit) as limN.
      replace limit with (Pos.of_nat limN) by (subst; apply Pos2Nat.id).
      assert (limN > 0)%nat as HNonZero by lia. clear HeqlimN.
      iInduction limN as [|limN'] "IH" forall (HNonZero); simpl in *. lia.
      inversion HNonZero.
      - by iDestruct "HEntries" as "[$ _]".
      - replace (S limN') with (1 + limN') by lia.
        rewrite Nat2Pos.inj_add; try lia.
        rewrite Cinl_op Some_op pair_op_2 auth_frag_op own_op.
        iDestruct "HEntries" as "[$ HEntries]".
        iApply ("IH" with "[%] HEntries"). lia.
    }
    iMod (own_update_2 with "H● H◯") as "H●".
    apply auth_update_dealloc, prod_local_update_2, ucmra_cancel_local_update, _.
    iAssert (|==> own γb (● (Pos.to_nat limit, Some (Cinr limit))) ∗
                  own γb (◯ (1, ε)) ∗ own γb (◯ (ε, Some (Cinr limit))))%I
            with "[H●]" as ">(H● & HInhabit & H◯)".
    {
      iMod (own_update with "H●") as "($ & $ & $)"; last done.
      apply auth_update_alloc, prod_local_update'=>/=.
      - apply nat_local_update. simpl. rewrite Nat.add_1_r Nat.add_0_r. lia.
      - by apply (alloc_option_local_update (Cinr limit)).
    }
    iAssert ([∗] replicate (Pos.to_nat limit) (barrier_exit_piece γb))%I
      with "[H◯]" as "HExit".
    {
      clear. remember (Pos.to_nat limit) as NLim.
      replace limit with (Pos.of_nat NLim) by (subst; apply Pos2Nat.id).
      assert (NLim > 0)%nat as HGt by (subst; lia). move: HGt. clear.
      intros HGt.
      iInduction (NLim) as [|NLim] "IH"; first lia.
      simpl.
      inversion HGt; first by iFrame. simplify_eq.
      replace (Pos.of_nat (S NLim)) with (1 + Pos.of_nat NLim)%positive;
        last by rewrite Nat2Pos.inj_succ; lia.
      rewrite Cinr_op Some_op pair_op_2 auth_frag_op own_op.
      iDestruct "H◯" as "[$ HFrag]". iApply ("IH" with "[//] HFrag").
    }
    remember (Pos.to_nat limit - 1)%nat as sleepers.
    replace (Pos.to_nat limit) with (S sleepers) by lia.
    simpl. iDestruct "HExit" as "[HMyExit HWakers]".
    iAssert (|={⊤ ∖ ↑NBar}=> thread_queue_state γtq 0 ∗
            [∗] replicate sleepers (awakening_permit γtq))%I
      with "[HState HWakers]" as ">[HState HAwaks]".
    {
      clear. iInduction (sleepers) as [|sleepers] "IH"=>/=. by iFrame.
      iDestruct "HWakers" as "[HWaker HWakers]".
      iMod (thread_queue_register_for_dequeue' with
                "HTq [$] [$]") as "[HState $]". by solve_ndisj.
      lia. rewrite /= Nat.sub_0_r.
      iApply ("IH" with "HState HWakers").
    }
    iSplitR "HΦ HAwaks HMyExit HInhabit".
    { iExists (S sleepers). rewrite /barrier_inv. subst. iSplitL "H●".
      { iRight; iFrame. iPureIntro; lia. }
      rewrite Z.add_1_r -Nat2Z.inj_succ.
      replace (S (_ - _)) with (Pos.to_nat limit) by lia.
      rewrite Nat.mod_same; last lia. simpl. iFrame "HState". done. }
    iModIntro. wp_pures.
    rewrite bool_decide_true; last by congr (fun x => LitV (LitInt x)); lia.
    wp_pures.
    wp_apply (forRange_resource_map
                (fun _ => awakening_permit γtq) (fun _ => True)%I
             with "[] [HAwaks]").
    + iIntros (i Ψ) "!> HAwak HΨ". wp_pures. wp_lam.
      wp_apply (resumeBarrier_spec with "[$]"). iIntros (_).
      by iApply "HΨ".
    + by rewrite -big_sepL_replicate seq_length.
    + iIntros (?) "_". wp_pures.
      iApply (fillThreadQueueFuture_spec with "[HMyExit]").
      2: { iIntros "!>" (γf v') "(H1 & H2 & _)". iApply "HΦ".
           iFrame "HInhabit H1 H2". }
      rewrite /V'. simpl. iExists _. iFrame. by iPureIntro.
  - iMod (thread_queue_append' with "HTq [] HState")
      as "[HState HSus]"=> /=; [by solve_ndisj|done|].
    iAssert (|==> own γb (● (S n, Some (Cinl limit))) ∗
                  own γb (◯ (1, ε)))%I with "[H●]" as ">[H● HInhabit]".
    { iMod (own_update with "H●") as "[$ $]"; last done.
      apply auth_update_alloc, prod_local_update_1, nat_local_update.
      rewrite Nat.add_0_r. lia. }
    wp_faa. iSplitR "HΦ HSus HInhabit".
    { iExists (S n). iModIntro. iSplitL "H●".
      + iLeft. iFrame. iPureIntro. lia.
      + rewrite Nat.mod_small; last lia. iFrame.
        by replace (n + 1)%Z with (Z.of_nat (S n)) by lia. }
    iModIntro. wp_pures. rewrite bool_decide_false; last by case; lia.
    wp_pures. wp_apply (suspend_spec with "[$]")=>/=.
    iIntros (v) "[(_ & _ & %)|Hv]"; first done.
    iDestruct "Hv" as (γf v' ->) "[HFuture HCancPermit]".
    wp_pures. iApply "HΦ". iFrame.
Qed.

Theorem cancelBarrierFuture_spec γb γa γtq γe γd s γf f:
  is_barrier γb γa γtq γe γd s -∗
  is_barrier_future γb γtq γa γf f -∗
  <<< ▷ thread_queue_future_cancellation_permit γf ∗
      barrier_inhabitant_permit γb >>>
    cancelBarrierFuture array_interface limit s f @ ⊤ ∖ ↑NFuture ∖ ↑N
  <<< ∃ (r: bool),
      if r then future_is_cancelled γf
      else (∃ v, ▷ future_is_completed γf v) ∗
           thread_queue_future_cancellation_permit γf ∗
           barrier_inhabitant_permit γb, RET #r >>>.
Proof.
  iIntros "#HIsBar #HFuture" (Φ) "AU".
  iDestruct "HIsBar" as (e d p ->) "[HInv HTq]". wp_lam. wp_pures. wp_lam.
  wp_pures. awp_apply (try_cancel_thread_queue_future with "HTq HFuture");
              first by solve_ndisj.
  iApply (aacc_aupd_commit with "AU"). by solve_ndisj.
  iIntros "[HCancPermit HInhabit]". iAaccIntro with "HCancPermit".
  by iIntros "$ !>"; iFrame; iIntros "$ !>".
  iIntros (r) "Hr". iExists r. destruct r.
  2: { iDestruct "Hr" as "[$ $]". iFrame. iIntros "!> HΦ !>". by wp_pures. }
  iDestruct "Hr" as "[#HFutureCancelled Hr]". iFrame "HFutureCancelled".
  rewrite /is_barrier_future /is_thread_queue_future.
  iDestruct "Hr" as (i f' s ->) "Hr"=> /=.
  iDestruct "Hr" as "(#H↦~ & #HTh & HToken)". iIntros "!> HΦ !>". wp_pures.
  wp_lam. wp_pures. wp_apply derefCellPointer_spec.
  by iDestruct "HTq" as "(_ & $ & _)". iIntros (ℓ) "#H↦". wp_pures.
  iLöb as "IHCancAllowed".
  wp_bind (!_)%E.
  iInv "HInv" as (n) "(>[[% H●]|[-> H●]] & Hℓ & HEntries & HState)" "HClose".
  2: {
    wp_load. rewrite Nat.mod_same; last lia.
    iMod (register_cancellation with "HTq HToken HState")
        as "[HCancToken HState]"; first by solve_ndisj.
    iDestruct "HState" as "(HState & HR & #HInhabited)".
    iMod ("HClose" with "[-HΦ HCancToken HR]") as "_".
    { iExists (Pos.to_nat limit). iSplitL "H●".
      - iRight. by iFrame.
      - rewrite Nat.mod_same; last lia. iFrame. }
    iModIntro. wp_pures. rewrite bool_decide_true; last done. wp_pures.
    wp_bind (getAndSet.getAndSet _ _).
    awp_apply (markRefused_spec with "HTq HInhabited H↦ HCancToken HTh [//]")
              without "HΦ HR".
    iAaccIntro with "[//]"; first done. iIntros (v) "Hv"=>/=.
    iIntros "!> [HΦ HR]". iDestruct "Hv" as "[[-> _]|Hv]"; first by wp_pures.
    iDestruct "Hv" as (? ->) "[_ >%]". simplify_eq. wp_pures.
    iApply "HΦ". (* we are losing the exit barrier piece here. *)
  }
  wp_load.
  iMod ("HClose" with "[-HΦ HToken HInhabit]") as "_".
  { iExists _. iSplitL "H●"; first by iLeft; iFrame. iFrame. }
  iModIntro. wp_pures. rewrite bool_decide_false; last by case; lia.
  wp_pures. wp_bind (CmpXchg _ _ _).
  iInv "HInv" as (n') "(>[[% H●]|[-> H●]] & Hℓ & HEntries & >HState)" "HClose".
  2: {
    wp_cmpxchg_fail. by case; lia.
    iMod ("HClose" with "[-HΦ HToken HInhabit]") as "_".
    { iExists _. iSplitL "H●"; first by iRight; iFrame. iFrame. }
    iModIntro. wp_pures. by iApply ("IHCancAllowed" with "HInhabit HToken HΦ").
  }
  destruct (decide (n = n')) as [<-|HNe].
  2: {
    wp_cmpxchg_fail; first by intro HContra; simplify_eq.
    iMod ("HClose" with "[-HΦ HToken HInhabit]") as "_".
    { iExists _. iSplitL "H●"; first by iLeft; iFrame. iFrame. }
    iModIntro. wp_pures. by iApply ("IHCancAllowed" with "HInhabit HToken HΦ").
  }
  iAssert (⌜(n > 0)%nat⌝)%I with "[-]" as %HN'Gt.
  { iDestruct (own_valid_2 with "H● HInhabit") as
        %[[HOk%nat_included _]%prod_included _]%auth_both_valid.
    iPureIntro; simpl in *; lia. }
  iMod (register_cancellation with "HTq HToken HState")
       as "[HCancToken HState]"; first by solve_ndisj.
  rewrite bool_decide_false Nat.mod_small; try lia. wp_cmpxchg_suc.
  iDestruct "HState" as "(HState & HCancHandle & #HInhabited)".
  iMod (own_update_2 with "H● HInhabit") as "H●".
  { apply auth_update_dealloc, prod_local_update_1.
    apply (nat_local_update _ _ (n - 1)).
    rewrite Nat.add_0_r Nat.add_1_r. lia. }
  destruct n as [|n']; first lia.
  iDestruct "HEntries" as "[HEntry HEntries]".
  iMod ("HClose" with "[-HΦ HCancToken HCancHandle HEntry]") as "_".
  {
    rewrite Nat.sub_1_r=>/=.
    iExists n'. iSplitL "H●". by iLeft; iFrame; iPureIntro; lia.
    rewrite Nat.mod_small; last lia. iFrame.
    by rewrite Z.sub_1_r -Nat2Z.inj_pred/=.
  }
  iModIntro. wp_pures. wp_bind (getAndSet.getAndSet _ _).
  awp_apply (markCancelled_spec with "HTq HInhabited H↦ HCancToken HTh")
            without "HΦ HCancHandle HEntry".
  iAaccIntro with "[//]"; first done. iIntros (v) "Hv"=>/=.
  iIntros "!> (HΦ & HCancHandle & HEntry)". wp_pures.
  iAssert (▷ cell_cancellation_handle _ _ _ _ _ _)%I
          with "[HCancHandle]" as "HCancHandle"; first done.
  awp_apply (cancelCell_spec with "[] H↦~") without "Hv HΦ".
  by iDestruct "HTq" as "(_ & $ & _)".
  iAaccIntro with "HCancHandle". by iIntros "$".
  iIntros "#HCancelled !> [Hv HΦ]". wp_pures.
  iDestruct "Hv" as "[[-> _]|Hv]"; first by wp_pures.
  iDestruct "Hv" as (x ->) "(#HInhabited' & HAwak & %)"; simplify_eq.
  wp_pures. wp_apply (resumeBarrier_spec with "[$]").
  iIntros "_". wp_pures. iApply "HΦ".
  (* we are losing the entry barrier piece, but it's not a big deal since the *)
  (* API does not provide a way to learn whether the cancellation succeeded *)
  (* before or after a thread arrived to resume everything. *)
Qed.

End proof.
