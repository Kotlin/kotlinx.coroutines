From iris.heap_lang Require Import notation.
From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import proofmode.
From iris.algebra Require Import auth.
From iris.algebra Require Import list gset excl csum.
From iris.program_logic Require Import atomic.
Require Import SegmentQueue.lib.thread_queue.thread_queue.
Require Import SegmentQueue.lib.infinite_array.infinite_array_impl.
Require Import SegmentQueue.lib.infinite_array.iterator.
Require Import SegmentQueue.lib.util.interruptibly.
Require Import SegmentQueue.util.everything.

Section proof.

Context `{iArrayG Σ} `{iteratorG Σ} `{heapG Σ} `{threadQueueG Σ}
        `{parkingG Σ} `{interruptiblyG Σ}.

Variable (N Nth: namespace).
Variable (segment_size: positive).

Definition thread_queue_as_counter E R γa γtq γe γd eℓ epℓ dℓ dpℓ n :=
  (∃ l deqFront,
    is_thread_queue N Nth segment_size E R γa γtq γe γd eℓ epℓ dℓ dpℓ l deqFront ∗
                    ⌜n = count_matching still_present (drop deqFront l)⌝)%I.

Lemma try_deque_thread_as_counter_spec E R γa γtq γe γd (eℓ epℓ dℓ dpℓ: loc):
  ▷ awakening_permit γtq
    -∗
  <<< ∀ (n: nat), ▷ thread_queue_as_counter E R γa γtq γe γd eℓ epℓ dℓ dpℓ n >>>
    ((try_deque_thread segment_size) #dpℓ) #dℓ @ ⊤ ∖ ↑N
  <<< ∃ v : val, ▷ E ∗ ▷ thread_queue_as_counter E R γa γtq γe γd eℓ epℓ dℓ dpℓ n ∗
                   (⌜v = #()⌝ ∨
                    (∃ i γt (th: loc),
                        ⌜v = #th⌝ ∧ ▷ rendezvous_thread_handle Nth γtq γt th i ∗
                                      (resumer_token γtq i ∗ rendezvous_resumed γtq i ∨
                                       thread_doesnt_have_permits γt)
                   )), RET v >>>.
Proof.
  iIntros "HAwak" (HΦ) "AU".
  awp_apply (try_deque_thread_spec with "HAwak").
  iApply (aacc_aupd_commit with "AU"); first done.
  iIntros (n) "HTq".
  iDestruct "HTq" as (l deqFront) "[HTq >->]".
  iAaccIntro with "HTq".
  {
    iIntros "HTq !>". iSplitL; first by iExists _, _; iFrame.
    iIntros "$ //".
  }
  iIntros (v) "[$ HState]". iExists _; iSplitL; last by iIntros "!> $".
  iDestruct "HState" as (i) "[HState|HState]".
  - iDestruct "HState" as "[(HEl & -> & HTq) HRend]".
    iDestruct "HEl" as %HEl.
    iSplitL "HTq"; last by iLeft.
    destruct (decide (i < deqFront)%nat).
    2: {
      iDestruct "HTq" as "(_ & (_ & >HResumerStage & _) & _)".
      rewrite big_sepL_forall.
      iSpecialize ("HResumerStage" $! (i - deqFront)%nat _ with "[]").
      {
        iPureIntro.
        rewrite lookup_drop.
        replace (deqFront + (i - deqFront))%nat with i by lia.
        rewrite list_lookup_alter.
        rewrite HEl. done.
      }
      simpl.
      iDestruct "HResumerStage" as %HContra.
      discriminate.
    }
    iExists _, deqFront.
    iFrame.
    iPureIntro.
    by rewrite drop_alter.
  - iDestruct "HState" as (γt th) "[#HThreadHandle [HState|HState]]".
    2: {
      iDestruct "HState" as "[HState (-> & HTq & HNoPerms)]".
      iSplitL "HTq"; first by iExists _, _; iFrame.
      iRight. iExists _, _, _. iSplitR; first by iPureIntro.
      iFrame "HThreadHandle". by iRight.
    }
    iDestruct "HState" as (HEl ->) "(HTq & #HRendRes & HResTok)".
    {
      destruct (decide (i < deqFront)%nat).
      2: {
        iDestruct "HTq" as "(_ & (_ & >HResumerStage & _) & _)".
        rewrite big_sepL_forall.
        iSpecialize ("HResumerStage" $! (i - deqFront)%nat _ with "[]").
        {
          iPureIntro.
          rewrite lookup_drop.
          replace (deqFront + (i - deqFront))%nat with i by lia.
          rewrite list_lookup_alter.
          rewrite HEl. done.
        }
        simpl.
        iDestruct "HResumerStage" as %HContra.

        discriminate.
      }
      iSplitL "HTq".
      { iExists _, _. iFrame. iPureIntro. by rewrite drop_alter. }
      iRight. iExists _, _, _. iSplitR; first by iPureIntro.
      iFrame "HThreadHandle".
      by iLeft; iFrame.
    }
Qed.

Lemma try_enque_thread_as_counter_spec E R γa γtq γe γd γt (eℓ epℓ dℓ dpℓ th : loc):
  is_thread_handle Nth γt #th -∗
  suspension_permit γtq -∗ thread_doesnt_have_permits γt -∗
  <<< ∀ (n: nat), ▷ thread_queue_as_counter E R γa γtq γe γd eℓ epℓ dℓ dpℓ n >>>
    (((try_enque_thread segment_size) #th) #epℓ) #eℓ @ ⊤ ∖ ↑N
  <<< ∃ v, ▷ thread_queue_as_counter E R γa γtq γe γd eℓ epℓ dℓ dpℓ n ∗
           ((∃ (i: nat) (s: loc),
             ⌜v = InjRV (#s, #(i `mod` Pos.to_nat segment_size)%nat)⌝ ∧
             segment_location γa (i `div` Pos.to_nat segment_size) s ∗
             rendezvous_thread_handle Nth γtq γt th i ∗ inhabitant_token γtq i
            ) ∨
            (⌜v = InjLV #()⌝ ∧ ▷ R ∗ thread_doesnt_have_permits γt)),
  RET v >>>.
Proof.
  iIntros "HTh HIsSus HNoPerms" (Φ) "AU".
  awp_apply (try_enque_thread_spec with "HTh HIsSus HNoPerms").
  iApply (aacc_aupd_commit with "AU"); first done.
  iIntros (n) "HTq".
  iDestruct "HTq" as (l deqFront) "[HTq >->]".
  iAaccIntro with "HTq".
  {
    iIntros "HTq !>". iSplitL; first by iExists _, _; iFrame.
    iIntros "$ //".
  }
  iIntros (v) "HPures".
  iExists v. iSplitL; last by iIntros "!> $".
  iDestruct "HPures" as "[HTq|(-> & HTq & HNoPerms & HR)]".
  2: {
    iSplitL "HTq". iExists _, _; by iFrame "HTq".
    iRight. by iFrame.
  }
  iDestruct "HTq" as (i s -> HEl) "(#HSegLoc & #HRend & HTq & HInhToken)".
  iSplitL "HTq"; last by iLeft; iExists i, s; iSplitR;
    [iPureIntro|iFrame "HSegLoc HRend HInhToken"].
  iExists _, _. iFrame.
  iPureIntro.
  destruct (decide (i < deqFront)%nat).
  by rewrite drop_alter //.
  repeat rewrite count_matching_drop.
  rewrite take_alter; try lia.
  erewrite count_matching_alter; eauto.
  simpl.
  lia.
Qed.

Lemma thread_queue_as_counter_append E R γa γtq γe γd (eℓ epℓ dℓ dpℓ : loc) n:
  E -∗ thread_queue_as_counter E R γa γtq γe γd eℓ epℓ dℓ dpℓ n
    ==∗ suspension_permit γtq ∗
    thread_queue_as_counter E R γa γtq γe γd eℓ epℓ dℓ dpℓ (S n).
Proof.
  iIntros "HE HTq".
  iDestruct "HTq" as (l deqFront) "[HTq ->]".
  iAssert (⌜(deqFront <= length l)%nat⌝)%I as %HDeqFront.
  {
    iDestruct "HTq" as "(_ & _ & _ & HRest)".
    iDestruct "HRest" as (? ?) "(_ & _ & _ & _ & %)".
    iPureIntro.
    lia.
  }
  iMod (thread_queue_append with "HE HTq") as "[[$ _] HTq]".
  iExists _, _. iFrame. iPureIntro.
  rewrite drop_app_le // count_matching_app /=. lia.
Qed.

Lemma thread_queue_as_counter_unpark_spec E R γa γtq γe γd γt (eℓ epℓ dℓ dpℓ: loc) (th: loc) i:
  rendezvous_resumed γtq i -∗
  is_thread_handle Nth γt #th -∗
  rendezvous_thread_locs_state γtq γt th i -∗
  <<< ∀ n, resumer_token γtq i ∗ ▷ thread_queue_as_counter E R γa γtq γe γd eℓ epℓ dℓ dpℓ n >>>
    unpark #th @ ⊤ ∖ ↑Nth
  <<< ▷ thread_queue_as_counter E R γa γtq γe γd eℓ epℓ dℓ dpℓ n, RET #() >>>.
Proof.
  iIntros "HRendRes HIsThread HThreadLocs" (Φ) "AU".
  awp_apply (thread_queue_unpark_spec with "HRendRes HIsThread HThreadLocs").
  iApply (aacc_aupd_commit with  "AU"); first done.
  iIntros (n) "[HResTok HTq]". iDestruct "HTq" as (? ?) "[HTq >->]".
  iCombine "HResTok" "HTq" as "HAacc".
  iAaccIntro with "HAacc".
  {
    iIntros "[$ HTq]". iSplitL; last by iIntros "!> $".
    iExists _, _. by iFrame.
  }
  iIntros "HTq".
  iSplitL; last by iIntros "!> $".
  iExists _, _. by iFrame.
Qed.

Lemma thread_as_counter_register_for_dequeue E R γa γtq γe γd (eℓ epℓ dℓ dpℓ : loc) n:
  (n > 0)%nat ->
  R -∗ thread_queue_as_counter E R γa γtq γe γd eℓ epℓ dℓ dpℓ n
    ==∗ awakening_permit γtq ∗
        thread_queue_as_counter E R γa γtq γe γd eℓ epℓ dℓ dpℓ (n - 1).
Proof.
  iIntros (HNPos) "HR HTq".
  iDestruct "HTq" as (l deqFront) "[HTq ->]".

  apply count_matching_find_index_Some in HNPos.
  destruct HNPos as [? HFindIndex].

  iDestruct "HTq" as "(HInfArr & HListContents & % & HRest)".
  iDestruct (cell_list_contents_register_for_dequeue
               with "HR HListContents") as ">[[$ #HDeqFront] [HListContents HCounts]]".
  by eauto.

  iExists _, _. iFrame "HListContents". iFrame.
  iSplitL "HRest".
  {
    iDestruct "HRest" as (enqIdx deqIdx) "(HIt1 & HIt2 & HAwaks & HSusps & %)".
    apply find_index_Some in HFindIndex.
    destruct HFindIndex as [[? [HC HPres]] HNotPres].
    rewrite lookup_drop in HC.
    iSplitR.
    {
      iPureIntro.
      intros [_ (? & ? & HOk)].
      replace (deqFront + S x - 1)%nat with (deqFront + x)%nat in HOk by lia.
      by simplify_eq.
    }
    iExists _, _. iFrame.
    iPureIntro.
    repeat split; try lia.
    assert (deqFront + x < length l)%nat; try lia.
    apply lookup_lt_is_Some. by eauto.
  }
  iDestruct "HCounts" as %HCounts.
  iPureIntro.
  rewrite HCounts. lia.
Qed.

Lemma do_cancel_rendezvous_as_counter_spec E R γa γtq γe γd (eℓ epℓ dℓ dpℓ : loc) (n i : nat):
  (n > 0)%nat ->
  inhabitant_token γtq i -∗
  ▷ thread_queue_as_counter E R γa γtq γe γd eℓ epℓ dℓ dpℓ n ==∗
  ▷ (thread_queue_as_counter E R γa γtq γe γd eℓ epℓ dℓ dpℓ (n - 1)%nat ∗
      (canceller_token γtq i ∗ rendezvous_cancelled γtq i
        ∨ (∃ ℓ : loc, array_mapsto segment_size γa i ℓ ∗ ▷ ℓ ↦ InjRV #0)
              ∗ awakening_permit γtq ∗ rendezvous_resumed γtq i)).
Proof.
  iIntros (HNGt) "HInhToken HTq".
  iDestruct "HTq" as (l deqFront) "[HTq >->]".
  apply count_matching_find_index_Some in HNGt.
  destruct HNGt as [? HFindIndex].

  iMod (do_cancel_rendezvous_spec with "HInhToken HTq") as (? ?) "HTT";
    first done.

  iDestruct "HTT" as "[(>HEl & HTq & HCancTok & #HRendCanc) |
    (>HEl & HTq & HLoc & HAwak & #HRendRes)]"; iDestruct "HEl" as %HEl.
  2: {
    iSplitR "HLoc HAwak"; last by iRight; iFrame.
    iExists _, _. iFrame.
    rewrite -drop_drop. remember (drop _ _) as l'.
    iPureIntro.
    rewrite count_matching_drop.
    by rewrite present_cells_in_take_Si_if_next_present_is_Si.
  }

  iSplitR "HCancTok"; last by iLeft; iFrame.
  iExists _, _. iFrame.
  iPureIntro.

  destruct (decide (i < deqFront)%nat) as [HLt|HGt].
  - rewrite drop_alter; last lia.
    rewrite -drop_drop. remember (drop deqFront l) as l'.
    rewrite count_matching_drop.
    rewrite present_cells_in_take_Si_if_next_present_is_Si //.
  - assert (deqFront <= i)%nat as HSum by lia.
    apply nat_le_sum in HSum. destruct HSum as [? ->].
    rewrite drop_alter'.
    erewrite count_matching_alter; last by rewrite lookup_drop.
    simpl.
    lia.
Qed.

Theorem thread_queue_as_counter_check_thread_permits_spec
        E R γa γtq γe γd (eℓ epℓ dℓ dpℓ: loc) i γth (threadHandle: loc) s:
  is_thread_handle Nth γth #threadHandle -∗
  segment_location γa (i `div` Pos.to_nat segment_size) s -∗
  rendezvous_thread_handle Nth γtq γth threadHandle i -∗
  <<< ∀ n, inhabitant_token γtq i ∗
           ▷ thread_queue_as_counter E R γa γtq γe γd eℓ epℓ dℓ dpℓ n >>>
    ! #threadHandle @ ⊤ ∖ ↑Nth
  <<< ∃ (r: bool), ▷ thread_queue_as_counter E R γa γtq γe γd eℓ epℓ dℓ dpℓ n ∗
                  (⌜r = true⌝ ∧ inhabitant_token γtq i
                   ∨ ⌜r = false⌝ ∧ thread_has_permit γth ∗ R), RET #r >>>.
Proof.
  iIntros "#HTh #HSegLoc #HRend" (Φ) "AU".
  awp_apply (thread_queue_check_thread_permits_spec with "[$] [$] [$]").
  iApply (aacc_aupd_commit with "AU"); first done.
  iIntros (n) "[HInh HTq]".
  iDestruct "HTq" as (? ?) "[HTq >->]".
  iCombine "HInh" "HTq" as "HAacc".
  iAaccIntro with "HAacc".
  {
    iIntros "[$ HTq] !>".
    iSplitL; first by iExists _, _; iFrame.
    iIntros "$ //".
  }
  iIntros (b) "[HTq HR]".
  iExists b. iSplitL; last by iIntros "!> $ //".
  iFrame "HR".
  by iExists _, _; iFrame.
Qed.

Theorem thread_queue_abandon_if_empty
  E R γa γtq γe γd (eℓ epℓ dℓ dpℓ: loc) i:
  inhabitant_token γtq i -∗
  thread_queue_as_counter E R γa γtq γe γd eℓ epℓ dℓ dpℓ O ==∗
  thread_queue_as_counter E R γa γtq γe γd eℓ epℓ dℓ dpℓ O ∗ R ∗
  (rendezvous_abandoned γtq i ∨ rendezvous_resumed γtq i).
Proof.
  iIntros "HInhTok HTq".
  iDestruct "HTq" as (l deqFront) "[HTq HH]". iDestruct "HH" as %HH.
  iDestruct "HTq" as "(HInfArr & (HL1 & HL2 & HLAuth & HL3) & HRest)".
  iDestruct (inhabited_cell_states with "HInhTok [$]") as
      %(γt & th & [HEl|HEl]).
  {
    destruct (decide (i < deqFront)%nat).
    2: { (* Can't happen: we are alive, but the counter says otherwise *)
      exfalso.
      assert (deqFront <= i)%nat as HSum by lia.
      apply nat_le_sum in HSum. destruct HSum as [z ->].
      rewrite -lookup_drop in HEl. remember (drop deqFront l) as l'.
      move: HH HEl. clear. intros.
      generalize dependent z.
      induction l'; intros z HEl. by inversion HEl.
      destruct z; simpl in *; first by simplify_eq.
      destruct (decide (still_present _)); try done.
      by eapply IHl'.
    }
    iMod (cell_list_contents__deq_front_at_least (S i) with "HLAuth") as
        "[HLAuth #HDeqFrontAtLeast]"; first by lia.
    iMod (abandon_rendezvous with "HDeqFrontAtLeast HInhTok [$]")
      as "[HH $]".
    iDestruct "HH" as (? ?) "[(HEl' & HListContents & $)|
                              (HContra & _)]".
    2: {
      iDestruct "HContra" as %HContra.
      simplify_eq.
    }
    iExists _, _. iFrame.
    rewrite alter_length. iDestruct "HRest" as "[HRest $]".
    rewrite drop_alter //. iSplitL; last done.
    iDestruct "HRest" as %HRest. iPureIntro.
    destruct (decide (i = deqFront - 1)%nat).
    - subst. rewrite list_lookup_alter.
      rewrite HEl. simpl. intros [_ (? & ? & HContra)].
      simplify_eq.
    - by rewrite list_lookup_alter_ne.
  }
  iMod (rendezvous_done_from_auth with "HLAuth") as "[HLAuth #HDone]".
  done. by eauto.
  iDestruct (cell_list_contents_lookup_acc with "[$]")
            as "[HRR HListRestore]"; first done.
  simpl.
  iDestruct "HRR" as (ℓ) "(HArrMapsto & HRendTh & HIsSus & HIsRes &
    HCancHandle & [[HInhTok' _]|(Hℓ & $ & [[HHasPerm HResTok]|HNoPerms])])".
  by iDestruct (inhabitant_token_exclusive with "HInhTok HInhTok'") as %[].
  {
    iDestruct ("HListRestore" with "[HArrMapsto HRendTh HIsSus HIsRes
      HCancHandle HResTok HInhTok]") as "HLC".
    { iExists _. iFrame. iLeft. iFrame. }
    iSplitL; last by iRight; iFrame; iExists _, _; iFrame "HDone".
    iExists _, _.
    by iFrame.
  }
  {
    iDestruct ("HListRestore" with "[HArrMapsto HRendTh HIsSus HIsRes
      HCancHandle HInhTok HNoPerms]") as "HLC".
    by iExists _; iFrame.
    iSplitL; last by iRight; iFrame; iExists _, _; iFrame "HDone".
    iExists _, _. by iFrame.
  }
Qed.

End proof.
