Require Import SegmentQueue.lib.thread_queue.thread_queue.
From SegmentQueue.lib.concurrent_linked_list.infinite_array
     Require Import array_spec iterator.iterator_impl.
Require Import SegmentQueue.lib.util.future.
From iris.heap_lang Require Import notation.

Section impl.

Variable array_interface: infiniteArrayInterface.

Definition newSemaphore: val :=
  λ: "n", (ref "n", newThreadQueue array_interface #()).

Definition acquireSemaphore: val :=
  λ: "sem",
  let: "availablePermits" := Fst ("sem") in
  let: "e" := Fst (Snd ("sem")) in
  let: "p" := FAA "availablePermits" #(-1) in
  if: #0 < "p" then fillThreadQueueFuture #()
  else suspend array_interface "e".

Definition semaphoreResume: val :=
  λ: "d", resume array_interface #(Z.of_nat 300) #true #true #false "d"
                 (λ: <>, #()) #().

Definition releaseSemaphore: val :=
  λ: "sem",
  let: "availablePermits" := Fst ("sem") in
  let: "d" := Snd (Snd ("sem")) in
  let: "p" := FAA "availablePermits" #1 in
  if: #0 ≤ "p" then #()
  else semaphoreResume "d".

Definition cancelSemaphoreFuture : val :=
  λ: "sem" "f",
  let: "availablePermits" := Fst ("sem") in
  let: "d" := Snd (Snd ("sem")) in
  tryCancelThreadQueueFuture' array_interface
                              #false #(Z.of_nat 300) #true #true #false
                              "d" (λ: <>, FAA "availablePermits" #1 < #0)
                              (λ: <>, #()) (λ: <>, releaseSemaphore "sem").

End impl.

From SegmentQueue.util Require Import everything big_opL.
From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import auth.
From iris.algebra Require Import list gset excl csum.
From iris.program_logic Require Import atomic.
From iris.heap_lang Require Import proofmode.

Section proof.

Context `{heapG Σ} `{iteratorG Σ} `{threadQueueG Σ} `{futureG Σ}.
Variable (N NFuture: namespace).
Variable (HNDisj: N ## NFuture).
Let NSem := N .@ "Sem".
Let NTq := N .@ "Tq".
Notation iProp := (iProp Σ).

Definition semaphore_inv (R: iProp) (γtq: gname) (availablePermits: nat)
           (p: loc) : iProp :=
 ([∗] replicate availablePermits R) ∗
 ∃ enqueuedThreads, thread_queue_state γtq enqueuedThreads ∗
 p ↦ #(availablePermits - enqueuedThreads) ∗
 ⌜availablePermits = 0 ∨ enqueuedThreads = 0⌝.

Variable array_interface: infiniteArrayInterface.
Variable array_spec: infiniteArraySpec _ array_interface.

Let tqParams R :=
  @ThreadQueueParameters Σ false True R True (fun v => ⌜#v = #()⌝)%I True.

Let isThreadQueue R := is_thread_queue NTq NFuture (tqParams R) _ array_spec.

Definition is_semaphore R γa γtq γe γd (s: val): iProp :=
  ∃ e d (p: loc), ⌜s = (#p, (e, d))%V⌝ ∧
  inv NSem (∃ availablePermits, semaphore_inv R γtq availablePermits p)
  ∗ isThreadQueue R γa γtq γe γd e d.

Theorem newSemaphore_spec (n: nat) R:
  {{{ inv_heap_inv ∗ [∗] replicate n R }}}
    newSemaphore array_interface #n
  {{{ γa γtq γe γd s, RET s; is_semaphore R γa γtq γe γd s }}}.
Proof.
  iIntros (Φ) "[#HHeap HR] HΦ". wp_lam. wp_bind (newThreadQueue _ _).
  iApply (newThreadQueue_spec with "HHeap").
  iIntros (γa γtq γe γd e d) "!> [#HTq HThreadState]".
  rewrite -wp_fupd. wp_alloc p as "Hp". wp_pures.
  iMod (inv_alloc NSem _ (∃ a, semaphore_inv R γtq a p) with "[-HΦ]") as "#HInv".
  { iExists _. iFrame "HR". iExists 0. rewrite Z.sub_0_r. iFrame. by iRight. }
  iApply "HΦ". iExists _, _, _. iSplitR; first done. by iFrame "HInv HTq".
Qed.

Lemma resumeSemaphore_spec R maxWait γa γtq γe γd e d:
  {{{ isThreadQueue R γa γtq γe γd e d ∗ awakening_permit γtq }}}
    resume array_interface #(Z.of_nat maxWait) #true #true #false d (λ: <>, #())%V #()
  {{{ (r: bool), RET #r; if r then True else R }}}.
Proof.
  iIntros (Φ) "[#HTq HAwak] HΦ".
  iApply (resume_spec with "[] [HAwak]").
  5: { by iFrame "HTq HAwak". }
  by solve_ndisj. done. done.
  { simpl. iIntros (Ψ) "!> _ HΨ". wp_pures. by iApply "HΨ". }
  iIntros "!>" (r) "Hr". iApply "HΦ". simpl. destruct r; first done.
  by iDestruct "Hr" as "(_ & $ & _)".
Qed.

Theorem releaseSemaphore_spec R γa γtq γe γd s:
  {{{ is_semaphore R γa γtq γe γd s ∗ R }}}
    releaseSemaphore array_interface s
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "[#HIsSem HR] HΦ". wp_lam.
  iDestruct "HIsSem" as (e d p ->) "[HInv HTq]". wp_pures. wp_bind (FAA _ _).
  iInv "HInv" as (availablePermits) "[HRs HOpen]" "HClose".
  iDestruct "HOpen" as (enqueuedThreads) "(HState & Hp & >HPures)".
  iDestruct "HPures" as %HPures.
  destruct (decide (0 ≤ availablePermits - enqueuedThreads)%Z) as [HGe|HLt].
  - assert (enqueuedThreads = 0) as -> by lia. rewrite Z.sub_0_r.
    wp_faa. iMod ("HClose" with "[-HΦ]") as "_".
    { iExists (S availablePermits). iFrame "HR HRs". iExists 0.
      iFrame "HState". iSplitL; last by iPureIntro; lia.
      replace (availablePermits + 1)%Z with (Z.of_nat (S availablePermits))
        by lia.
      by rewrite Z.sub_0_r. }
    iModIntro. wp_pures. rewrite bool_decide_true; last lia. wp_pures.
    by iApply "HΦ".
  - iMod (thread_queue_register_for_dequeue' with "HTq [HR] HState")
      as "[HState HAwak]"; [by solve_ndisj|lia|by iFrame|].
    wp_faa. iMod ("HClose" with "[-HΦ HAwak]") as "_".
    { iExists availablePermits. iFrame "HRs". iExists (enqueuedThreads - 1).
      iFrame "HState". iSplitL; last by iPureIntro; lia.
      by replace (availablePermits - enqueuedThreads + 1)%Z with
          (availablePermits - (enqueuedThreads - 1)%nat)%Z by lia. }
    iModIntro. wp_pures. rewrite bool_decide_false; last lia. wp_pures.
    wp_lam. wp_pures. iApply (resumeSemaphore_spec with "[$]").
    iIntros "!>" (r) "Hr".
Abort.

Theorem acquire_semaphore_spec Nint R γ (p epℓ eℓ dpℓ dℓ: loc) γa γtq γe γd
        γi cancHandle γth (threadHandle: loc):
  is_interrupt_handle Nint γi cancHandle -∗
  is_thread_handle Nth γth #threadHandle -∗
  is_semaphore R γ p epℓ eℓ dpℓ dℓ γa γtq γe γd -∗
  inv (N .@ "permits") (∃ a, semaphore_permits γ a) -∗
  {{{ thread_doesnt_have_permits γth }}}
    (acquire_semaphore segment_size) cancHandle #threadHandle #p #epℓ #eℓ #dpℓ #dℓ
  {{{ (v: val), RET v;
      ⌜v = InjRV #()⌝ ∧ thread_doesnt_have_permits γth ∗ R ∨
      ⌜v = InjLV #()⌝ ∧ interrupted γi
  }}}.
Proof.
  iIntros "#HIntHandle #HThreadHandle #HSemInv #HPermInv".
  iIntros (Φ) "!> HNoPerms HΦ".

  wp_lam. wp_pures. wp_bind (FAA _ _).
  iInv "HSemInv" as (availablePermits v)
                      "(HPerms & >HAuth & HTq & Hp & >HPure)" "HInvClose".
  wp_faa.
  iInv "HPermInv" as (?) ">HFrag" "HPermsClose".
  iDestruct (own_valid_2 with "HAuth HFrag") as
        %[->%Excl_included%leibniz_equiv _]%auth_both_valid.
  remember (availablePermits - _)%Z as oldP.
  destruct (decide (0 < oldP)%Z).
  {
    iMod (own_update_2 with "HAuth HFrag") as "[HAuth HFrag]".
    {
      apply auth_update, option_local_update.
      apply (exclusive_local_update _ (Excl (availablePermits - 1)%nat)).
      done.
    }
    iMod ("HPermsClose" with "[HFrag]") as "_"; first by eauto.
    iDestruct "HPure" as %[->|HH].
    by lia.
    destruct availablePermits; simpl in *; first by lia.
    iDestruct "HPerms" as "[HR HPerms]".
    iSpecialize ("HΦ" with "[HNoPerms HR]").
    { iLeft. iFrame. eauto. }
    iMod ("HInvClose" with "[-HΦ]") as "_".
    {
      iExists _, _.
      rewrite Nat.sub_0_r big_opL_irrelevant_element' seq_length.
      replace (oldP + -1)%Z with (availablePermits - v)%Z by lia.
      iFrame.
      iPureIntro.
      eauto.
    }
    iModIntro. wp_pures. rewrite bool_decide_decide decide_True //. by wp_pures.
  }

  destruct availablePermits.
  2: by iDestruct "HPure" as %[HContra|HOk]; lia.
  rewrite Z.sub_0_l in HeqoldP.
  subst.
  iClear "HPure".
  iMod (thread_queue_as_counter_append with "[$] HTq") as "[HIsSusp HTq]".
  iMod ("HPermsClose" with "[HFrag]") as "_"; first by eauto.
  iMod ("HInvClose" with "[-HIsSusp HNoPerms HΦ]") as "_".
  {
    iExists _, _. iFrame. replace (0%nat - S v)%Z with (-v + - 1)%Z by lia.
    iFrame.
    iPureIntro. lia.
  }
  iModIntro. wp_pures. rewrite bool_decide_decide decide_False //. wp_pures.
  wp_lam. wp_pures. wp_lam. wp_pures.

  rewrite /is_semaphore.

  awp_apply (try_enque_thread_as_counter_spec (N.@"tq") with
                 "HThreadHandle HIsSusp HNoPerms") without "HΦ".
  iInv "HSemInv" as (? v') "(HPerms & >HAuth & HTq & Hp & >HPure)".
  iAaccIntro with "HTq".
  {
    iIntros "HTq !>". iSplitL; last done.
    iExists _, _. iFrame.
  }
  iIntros (?) "[HTq HPures]".
  iDestruct "HPures" as "[HPures|(-> & HR & HNoPerms)]".
  2: {
    iModIntro. iSplitR "HNoPerms HR".
    by iExists _, _; iFrame.
    iIntros "HΦ".
    wp_pures.
    iSpecialize ("HΦ" with "[-]").
    { iLeft. iFrame. eauto. }
    done.
  }
  iDestruct "HPures" as (i s ->) "(#HSegLoc & #HRend & HInhToken)".
  iSplitR "HInhToken"; first by iExists _, _; iFrame.

  iIntros "!> HΦ". wp_pures. wp_lam. wp_pures.
  wp_apply (interruptibly_spec _ (inhabitant_token γtq i)
                               (fun v => ⌜v = #()⌝ ∧ thread_doesnt_have_permits γth ∗ R)%I
                               (fun v => ⌜v = #()⌝ ∧ interrupted γi)%I
              with "[HInhToken]").
  {

    iFrame "HIntHandle HInhToken".
    iSplit.
    {
      iIntros (Φ') "!> HInhTok HΦ'". wp_pures. wp_bind (!_)%E.
      rewrite /is_thread_handle.
      awp_apply (thread_queue_as_counter_check_thread_permits_spec with
                     "HThreadHandle HSegLoc HRend") without "HΦ'".
      iInv "HSemInv" as (? ?) "(HPerms & >HAuth & HTq & HRest)".
      iCombine "HInhTok" "HTq" as "HAacc".
      iAaccIntro with "HAacc".
      { iIntros "[$ HTq]". by iExists _, _; iFrame. }
      iIntros (b) "[HTq HRes] !>".
      iSplitR "HRes".
      by iExists _, _; iFrame.
      iIntros "HΦ".
      iDestruct "HRes" as "[[-> HInh]|(-> & HPerm & HR)]".
      all: wp_pures.
      - iApply "HΦ".
        iLeft; by iFrame.
      - iAssert (▷ thread_has_permit γth)%I with "[$]" as "HHasPerm".
        iClear "HIntHandle HSemInv HPermInv HSegLoc HRend". clear.
        awp_apply (thread_update_state _ _ _ true with "HThreadHandle") without "HΦ HR".
        iAaccIntro with "HHasPerm".
        by iIntros "$ //".
        iIntros "HNoPerms !> [HΦ HR]".
        wp_pures. iApply "HΦ".
        iRight; iFrame. by iExists _.
    }
    {
      iIntros (Φ') "!> [HInhTok #HInterrupted] HΦ'". wp_pures. wp_bind (FAA _ _).
      move: namespaces_disjoint. clear. intros.
      iInv "HSemInv" as (availablePermits v)
                          "(HPerms & >HAuth & HTq & Hp & >HPure)" "HInvClose".

      remember (availablePermits - _)%Z as oldP.
      destruct (decide (0 <= oldP)%Z) as [HLt|HGt].
      {
        wp_faa.
        iInv "HPermInv" as (?) ">HFrag" "HPermsClose".
        iDestruct (own_valid_2 with "HAuth HFrag") as
              %[->%Excl_included%leibniz_equiv _]%auth_both_valid.
        iMod (own_update_2 with "HAuth HFrag") as "[HAuth HFrag]".
        {
          apply auth_update, option_local_update.
          apply (exclusive_local_update _ (Excl (availablePermits + 1)%nat)).
          done.
        }
        iMod ("HPermsClose" with "[HFrag]") as "_"; first by eauto.
        iAssert (⌜v = 0%nat⌝)%I as %->.
        by iDestruct "HPure" as %[HH|HH]; subst; iPureIntro; lia.
        subst. rewrite Z.sub_0_r.
        iMod (thread_queue_abandon_if_empty with "HInhTok HTq")
          as "(HTq & HR & #HDone)".
        iMod ("HInvClose" with "[-HΦ']") as "_".
        {
          iExists _, _. iFrame. rewrite seq_add big_sepL_app /=. iFrame.
          iSplitL; last by iPureIntro; eauto.
          by rewrite Z.sub_0_r Nat2Z.inj_add.
        }
        iModIntro. wp_pures. rewrite bool_decide_decide decide_True //; last lia.
        wp_pures.
        iApply "HΦ'".
        iLeft. by iFrame "HInterrupted".
      }

      iMod (do_cancel_rendezvous_as_counter_spec with "HInhTok HTq")
        as "[HTq HTT]"; first by lia.

      wp_faa.

      iDestruct "HTT" as "[(HCancTok & #HRendCanc) | (HLoc & HAwak & #HRendRes)]".
      2: {
        iMod ("HInvClose" with "[-HΦ' HAwak HLoc]") as "_".
        {
          iExists _, _. iFrame.
          iSplitR "HPure"; last by iDestruct "HPure" as "[->|%]"; iPureIntro; lia.
          subst.
          by replace (availablePermits - v + 1)%Z
            with (availablePermits - (v - 1)%nat)%Z by lia.
        }
        iModIntro. wp_pures. rewrite bool_decide_decide decide_False //.
        wp_pures. wp_lam. wp_lam. wp_pures.

        awp_apply (segment_data_at_spec) without "HΦ' HLoc HAwak".
        by iPureIntro; apply Nat.mod_upper_bound; lia.
        iInv "HSemInv" as (? ?) "(HHead1 & HHead2 & HTq & HTail)".
        iDestruct "HTq" as (? ?) "[(HInfArr & HTail') HTail'']".
        iDestruct (is_segment_by_location with "HSegLoc HInfArr")
          as (? ?) "[HIsSeg HInfArrRestore]".
        iAaccIntro with "HIsSeg".
        {
          iIntros "HIsSeg".
          iDestruct ("HInfArrRestore" with "HIsSeg") as "HInfArr".
          iIntros "!>". iSplitL; last done.
          iExists _, _. iFrame. iExists _, _. iFrame.
        }

        iIntros (?) "(HIsSeg & #HArrMapsto & #HCellInv)".
        iDestruct (bi.later_wand with "HInfArrRestore HIsSeg") as "HInfArr".
        iSplitL; first by iExists _, _; iFrame; iExists _, _; iFrame.
        iIntros "!> (HΦ' & HLoc & HAwak)". wp_pures.

        iDestruct "HLoc" as (ℓ) "[#HArrMapsto' Hℓ]".
        iDestruct (array_mapsto'_agree with "HArrMapsto HArrMapsto'") as %->.
        iAssert (▷ ℓ ↦ RESUMEDV)%I with "Hℓ" as "Hℓ".
        awp_apply getAndSet.getAndSet_spec without "HΦ' HAwak".
        iAssert (▷ ℓ ↦ RESUMEDV ∧ ⌜val_is_unboxed RESUMEDV⌝)%I
          with "[Hℓ]" as "HAacc".
        by iFrame.
        iAaccIntro with "HAacc".
        by iIntros "[$ _]".
        iIntros "Hℓ !> [HΦ' HAwak]".
        wp_pures.
        wp_apply (resume_in_semaphore_spec with "[$] [$] [$]").
        iIntros "_". wp_pures. iApply "HΦ'". iLeft. by iFrame "HInterrupted".
      }

      iMod ("HInvClose" with "[-HΦ' HCancTok]") as "_".
      {
        iExists _, _. iFrame.
        iSplitL "Hp"; last by iDestruct "HPure" as "[->|%]"; by (iPureIntro; lia).
        subst.
        by replace (availablePermits - v + 1)%Z with
            (availablePermits - (v - 1)%nat)%Z by lia.
      }

      iModIntro. wp_pures. rewrite bool_decide_decide decide_False //. wp_pures.
      awp_apply (cancel_cell_spec with "HRendCanc HSegLoc HCancTok") without "HΦ'".
      iInv "HSemInv" as (? ?) "(HHead1 & HHead2 & HTq & HTail)".
      iDestruct "HTq" as (? ?) "[HTq HTail'']".
      iAaccIntro with "HTq".
      {
        iIntros "HTq !>". iSplitL; last done. iExists _, _. iFrame.
        iExists _, _. iFrame.
      }
      iIntros (b) "[HTq HRes] !>".
      iSplitR "HRes".
      { iExists _, _. iFrame. iExists _, _. iFrame. }
      iIntros "HΦ'".
      iDestruct "HRes" as "[(-> & HAwak)|->]"; wp_pures.
      wp_apply (resume_in_semaphore_spec with "[$] [$] [$]").
      iIntros "_"; wp_pures.
      all: iApply "HΦ'"; iLeft; by iFrame "HInterrupted".
    }
  }
  iIntros (? ?) "[(-> & [-> #HInterrupted])|(-> & -> & HHasPerm & HR)]".
  1: by wp_pures; iApply "HΦ"; iRight; eauto.
  iApply "HΦ". iLeft. iFrame. done.
Qed.

End proof.
