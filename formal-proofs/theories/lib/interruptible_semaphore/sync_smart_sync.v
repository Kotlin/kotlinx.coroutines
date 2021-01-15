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
  rec: "loop" "sem" :=
    let: "availablePermits" := Fst ("sem") in
    let: "e" := Fst (Snd ("sem")) in
    let: "p" := FAA "availablePermits" #(-1) in
    if: #0 < "p" then fillThreadQueueFuture #()
    else match: suspend array_interface "e" with
             NONE => "loop" "sem"
           | SOME "v" => "v"
         end.

Definition semaphoreResume: val :=
  λ: "d", resume array_interface #(Z.of_nat 300) #true #true #true "d"
                 (λ: <>, #()) #().

Definition releaseSemaphore: val :=
  rec: "loop" "sem" :=
    let: "availablePermits" := Fst ("sem") in
    let: "d" := Snd (Snd ("sem")) in
    let: "p" := FAA "availablePermits" #1 in
    if: #0 ≤ "p" then #()
    else if: semaphoreResume "d"
         then #()
         else "loop" "sem".

Definition cancelSemaphoreFuture : val :=
  λ: "sem" "f",
  let: "availablePermits" := Fst ("sem") in
  let: "d" := Snd (Snd ("sem")) in
  tryCancelThreadQueueFuture' array_interface
                              #false #(Z.of_nat 300) #true #true
                              "d" (λ: <>, FAA "availablePermits" #1 < #0)
                              (λ: <>, #()) (λ: <>, releaseSemaphore "sem") "f".

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

Definition is_semaphore_future R :=
  is_thread_queue_future NTq NFuture (tqParams R) _ array_spec.

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

Lemma resumeSemaphore_spec R maxWait (wait: bool) γa γtq γe γd e d:
  {{{ isThreadQueue R γa γtq γe γd e d ∗ awakening_permit γtq }}}
    resume array_interface #(Z.of_nat maxWait) #true #true #wait d (λ: <>, #())%V #()
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
  iIntros (Φ) "[#HIsSem HR] HΦ". wp_lam. iLöb as "IH".
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
    wp_lam. wp_pures. wp_apply (resumeSemaphore_spec with "[$]").
    iIntros (r) "Hr".
    destruct r; wp_pures. by iApply "HΦ".
    wp_lam. iApply ("IH" with "Hr HΦ").
Qed.

Theorem acquireSemaphore_spec R γa γtq γe γd s:
  {{{ is_semaphore R γa γtq γe γd s }}}
    acquireSemaphore array_interface s
  {{{ γf v, RET v; is_semaphore_future R γtq γa γf v ∗
                   thread_queue_future_cancellation_permit γf }}}.
Proof.
  iIntros (Φ) "#HIsSem HΦ". wp_lam. iLöb as "IH".
  iDestruct "HIsSem" as (e d p ->) "[HInv HTq]". wp_pures. wp_bind (FAA _ _).
  iInv "HInv" as (availablePermits) "[HRs HOpen]" "HClose".
  iDestruct "HOpen" as (enqueuedThreads) "(HState & Hp & >HPures)".
  iDestruct "HPures" as %HPures.
  destruct (decide (0 < availablePermits - enqueuedThreads)%Z) as [HGe|HLt].
  - assert (enqueuedThreads = 0) as -> by lia. rewrite Z.sub_0_r.
    destruct availablePermits as [|availablePermits']=> /=; first lia.
    iDestruct "HRs" as "[HR HRs]".
    wp_faa. iMod ("HClose" with "[-HΦ HR]") as "_".
    { iExists availablePermits'. iFrame "HRs". iExists 0.
      iFrame "HState". iSplitL; last by iPureIntro; lia.
      replace (S availablePermits' + -1)%Z with (Z.of_nat availablePermits')
        by lia.
      by rewrite Z.sub_0_r. }
    iModIntro. wp_pures. iApply (fillThreadQueueFuture_spec with "[HR]").
    2: {
      iIntros "!>" (γf v') "(HFuture & HCancPermit & _)".
      iApply "HΦ". iFrame.
    }
    rewrite /V'. iExists _. iSplitR; first done. simpl.
    iSplitR; first done. iFrame.
  - iMod (thread_queue_append' with "HTq [] HState")
      as "[HState HSus]"=> /=; [by solve_ndisj|done|].
    wp_faa. iMod ("HClose" with "[-HΦ HSus]") as "_".
    { iExists availablePermits. iFrame "HRs". iExists (S enqueuedThreads).
      iFrame "HState". iSplitL; last by iPureIntro; lia.
      by replace (availablePermits - enqueuedThreads + -1)%Z with
          (availablePermits - S enqueuedThreads)%Z by lia. }
    iModIntro. wp_pures. rewrite bool_decide_false; last lia. wp_pures.
    wp_apply (suspend_spec with "[$]")=> /=. iIntros (v) "[[-> _]|Hv]".
    + wp_pures. wp_lam. iApply ("IH" with "HΦ").
    + iDestruct "Hv" as (γf v') "(-> & HFuture & HCancPermit)". wp_pures.
      iApply "HΦ". iFrame.
Qed.

Theorem cancelSemaphoreFuture_spec R γa γtq γe γd s γf f:
  is_semaphore R γa γtq γe γd s -∗
  is_semaphore_future R γtq γa γf f -∗
  <<< ▷ thread_queue_future_cancellation_permit γf >>>
    cancelSemaphoreFuture array_interface s f @ ⊤ ∖ ↑NFuture ∖ ↑N
  <<< ∃ (r: bool),
      if r then future_is_cancelled γf
      else (∃ v, ▷ future_is_completed γf v) ∗
           thread_queue_future_cancellation_permit γf, RET #r >>>.
Proof.
  iIntros "#HIsSem #HFuture" (Φ) "AU".
  iDestruct "HIsSem" as (e d p ->) "[HInv HTq]". wp_lam. wp_pures. wp_lam.
  wp_pures. awp_apply (try_cancel_thread_queue_future with "HTq HFuture");
              first by solve_ndisj.
  iApply (aacc_aupd_commit with "AU"). by solve_ndisj.
  iIntros "HCancPermit". iAaccIntro with "HCancPermit". by iIntros "$ !> $ !>".
  iIntros (r) "Hr". iExists r. destruct r.
  2: { iDestruct "Hr" as "[$ $]". iIntros "!> HΦ !>". by wp_pures. }
  iDestruct "Hr" as "[#HFutureCancelled Hr]". iFrame "HFutureCancelled".
  rewrite /is_semaphore_future /is_thread_queue_future.
  iDestruct "Hr" as (i f' s ->) "Hr"=> /=.
  iDestruct "Hr" as "(#H↦~ & #HTh & HToken)". iIntros "!> HΦ !>". wp_pures.
  wp_lam. wp_pures. wp_apply derefCellPointer_spec.
  by iDestruct "HTq" as "(_ & $ & _)". iIntros (ℓ) "#H↦". wp_pures.
  wp_bind (FAA _ _).
  iInv "HInv" as (availablePermits) "[HRs HOpen]" "HClose".
  iDestruct "HOpen" as (enqueuedThreads) "(>HState & Hp & >HPures)".
  iDestruct "HPures" as %HPures.
  iMod (register_cancellation with "HTq HToken HState")
       as "[HCancToken HState]"; first by solve_ndisj.
  destruct (decide (availablePermits - enqueuedThreads < 0)%Z) as [HLt|HGe].
  - assert (availablePermits = 0) as -> by lia.
    destruct enqueuedThreads as [|enqueuedThreads']=>/=; first lia.
    iDestruct "HState" as "(HState & HCancHandle & #HInhabited)".
    wp_faa.
    iMod ("HClose" with "[-HΦ HCancToken HCancHandle]") as "_".
    { iExists 0. iSplitR; simpl; first done. iExists enqueuedThreads'.
      rewrite Nat.sub_0_r. iFrame "HState". iSplitL; last by iLeft.
      by replace (0%nat - S enqueuedThreads' + 1)%Z
        with (0%nat - enqueuedThreads')%Z by lia. }
    iModIntro. wp_pures. wp_bind (getAndSet.getAndSet _ _).
    awp_apply (markCancelled_spec with "HTq HInhabited H↦ HCancToken HTh")
              without "HΦ HCancHandle".
    iAaccIntro with "[//]"; first done. iIntros (v) "Hv"=>/=.
    iIntros "!> [HΦ HCancHandle]". wp_pures.
    iAssert (▷ cell_cancellation_handle _ _ _ _ _ _)%I
            with "[HCancHandle]" as "HCancHandle"; first done.
    awp_apply (cancelCell_spec with "[] H↦~") without "Hv HΦ".
    by iDestruct "HTq" as "(_ & $ & _)".
    iAaccIntro with "HCancHandle". by iIntros "$".
    iIntros "#HCancelled !> [Hv HΦ]". wp_pures.
    iDestruct "Hv" as "[[-> _]|Hv]"; first by wp_pures.
    iDestruct "Hv" as (x ->) "(#HInhabited' & HAwak & %)"; simplify_eq.
    wp_pures. wp_apply (resumeSemaphore_spec with "[$]").
    iIntros (r) "Hr". destruct r; wp_pures; first done.
    wp_apply (releaseSemaphore_spec with "[Hr]").
    { iSplitR; last by iApply "Hr". iExists _, _, _.
      iSplitR; first done. iFrame "HInv HTq". }
    iIntros "_". by wp_pures.
  - rewrite bool_decide_true; last lia. assert (enqueuedThreads = 0) as -> by lia.
    simpl. iDestruct "HState" as "(HState & HR & #HInhabited)".
    wp_faa.
    iMod ("HClose" with "[-HΦ HCancToken]") as "_".
    { iExists (S availablePermits). iFrame "HR HRs". iExists 0.
      iFrame "HState". iSplitL; last by iRight.
      by replace (availablePermits - 0%nat + 1)%Z
        with (S availablePermits - 0%nat)%Z by lia. }
    iModIntro. wp_pures. rewrite bool_decide_false; last lia. wp_pures.
    wp_bind (getAndSet.getAndSet _ _).
    awp_apply (markRefused_spec with "HTq HInhabited H↦ HCancToken HTh [//]")
              without "HΦ".
    iAaccIntro with "[//]"; first done. iIntros (v) "Hv"=>/=.
    iIntros "!> HΦ". iDestruct "Hv" as "[[-> _]|Hv]"; first by wp_pures.
    iDestruct "Hv" as (? ->) "[_ >%]". simplify_eq. by wp_pures.
Qed.

End proof.
