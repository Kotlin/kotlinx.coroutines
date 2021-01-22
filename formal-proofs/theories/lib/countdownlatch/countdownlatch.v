Require Import SegmentQueue.lib.thread_queue.thread_queue.
From SegmentQueue.lib.concurrent_linked_list.infinite_array
     Require Import array_spec iterator.iterator_impl.
From SegmentQueue.lib.util Require Import future getAndUpdate forRange.
From iris.heap_lang Require Import notation.

Section impl.

Variable array_interface: infiniteArrayInterface.

Definition newLatch: val :=
  λ: "count", (ref "count", ref #0, newThreadQueue array_interface #()).

Definition latchResume: val :=
  λ: "d", resume array_interface #(Z.of_nat 300) #true #false #false "d"
                 (λ: <>, #()) #().

(* Differs from the canonical implementation to be able to ignore the size of the
   memory cell. *)
Definition addWaiter: val := λ: "waiters", FAA "waiters" #2.
Definition removeWaiter: val := λ: "waiters", FAA "waiters" #(-2).
Definition hasDoneMark: val := λ: "w", "w" `rem` #2 = #1.
Definition setDoneMark: val := λ: "w", "w" + #1.

Definition resumeWaiters: val :=
  λ: "latch",
  let: "waiters" := Snd (Fst "latch") in
  let: "d" := Snd (Snd "latch") in
  let: "w" := getAndUpdate
                "waiters"
                (λ: "cur",
                 if: hasDoneMark "cur"
                 then NONE
                 else SOME (setDoneMark "cur"))
  in match: "w" with
        NONE => #()
      | SOME "w'" => forRange ("w'" `quot` #2) (λ: <>, latchResume "d");; #()
     end.

Definition countDown: val :=
  λ: "latch",
  let: "counter" := Fst (Fst "latch") in
  let: "d" := Snd (Snd "latch") in
  let: "p" := FAA "counter" #(-1) in
  if: "p" - #1 ≤ #0 then resumeWaiters "latch" else #().

Definition await: val :=
  λ: "latch",
  let: "counter" := Fst (Fst "latch") in
  let: "waiters" := Snd (Fst "latch") in
  let: "e" := Fst (Snd "latch") in
  if: !"counter" ≤ #0 then fillThreadQueueFuture #()
  else let: "w" := addWaiter "waiters" in
       if: hasDoneMark "w" then fillThreadQueueFuture #()
       else match: suspend array_interface "e" with
              InjR "f" => "f"
            | InjL "x" => "undefined"
            end.

Definition cancelLatchFuture : val :=
  λ: "latch" "f",
  let: "waiters" := Snd (Fst "latch") in
  let: "onCancellation" :=
     λ: <>, let: "w" := removeWaiter "waiters" in ~ (hasDoneMark "w")
  in
  let: "d" := Snd (Snd "latch") in
  tryCancelThreadQueueFuture' array_interface
                              #false #(Z.of_nat 300) #false #false
                              "d" "onCancellation"
                              (λ: <>, #()) (λ: <>, #()) "f".

Definition getCount: val :=
  λ: "latch",
  let: "counter" := Fst (Fst "latch") in
  let: "c" := !"counter" in
  if: "c" ≤ #0 then #0 else "c".

End impl.

From SegmentQueue.util Require Import everything big_opL local_updates.
From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import numbers auth list gset excl csum.
From iris.program_logic Require Import atomic.
From iris.heap_lang Require Import proofmode.

Section proof.

Notation algebra := (authR (prodUR
                              natUR
                              (optionUR (csumR (exclR positiveR)
                                                (optionR (agreeR unitO)))))).

Class latchG Σ := BarrierG { barrier_inG :> inG Σ algebra }.
Definition latchΣ : gFunctors := #[GFunctor algebra].
Instance subG_latchΣ {Σ} : subG latchΣ Σ -> latchG Σ.
Proof. solve_inG. Qed.

Context `{heapG Σ} `{iteratorG Σ} `{threadQueueG Σ} `{futureG Σ} `{latchG Σ}.
Variable (N NFuture: namespace).
Variable (HNDisj: N ## NFuture).
Let NLatch := N .@ "Latch".
Let NTq := N .@ "Tq".
Notation iProp := (iProp Σ).

Variable array_interface: infiniteArrayInterface.
Variable array_spec: infiniteArraySpec _ array_interface.

Definition latch_broken γ := own γ (◯ (0, Some (Cinr ε))).

Definition latch_closed γ := own γ (◯ (0, Some (Cinr (Some (to_agree ()))))).

Definition latch_waiter_registered γ := own γ (◯ (1, ε)).

Definition latch_waiter_permit γ γf: iProp :=
  latch_waiter_registered γ ∨
  (∃ v, future_is_completed γf v).

Global Instance latch_broken_persistent: Persistent (latch_broken γ).
Proof. apply _. Qed.

Let tqParams γl :=
  @ThreadQueueParameters Σ false True (latch_broken γl) True
                         (fun v => ⌜#v = #()⌝)%I False.

Let isThreadQueue γl := is_thread_queue NTq NFuture (tqParams γl) _ array_spec.

Definition is_latch_future γl :=
  is_thread_queue_future NTq NFuture (tqParams γl) _ array_spec.

Lemma resumeLatch_spec R maxWait (wait: bool) γa γtq γe γd e d:
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

Definition latch_invariant (γl γtq: gname) (ℓ wℓ: loc) (n: nat) (w: nat): iProp :=
  wℓ ↦ #(w * 2)%nat ∗ thread_queue_state γtq w ∗
    (⌜n > 0⌝ ∧ own γl (● (w, Some (Cinl (Excl (Pos.of_nat n))))) ∗ ℓ ↦ #n ∨
     ⌜n = 0⌝ ∧ own γl (● (w, Some (Cinr None))) ∗
        (∃ n', ⌜(n' ≤ 0)%Z⌝ ∧ ℓ ↦ #n')) ∨
  wℓ ↦ #(w * 2 + 1)%nat ∗ thread_queue_state γtq 0 ∗
    ⌜n = 0⌝ ∗ own γl (● (w, Some (Cinr (Some (to_agree ()))))) ∗
    (∃ n', ⌜(n' ≤ 0)%Z⌝ ∧ ℓ ↦ #n').

Definition is_latch γl γa γtq γe γd (s: val): iProp :=
  ∃ e d (p pw: loc), ⌜s = (#p, #pw, (e, d))%V⌝ ∧
  inv NLatch (∃ n w, latch_invariant γl γtq p pw n w)
  ∗ isThreadQueue γl γa γtq γe γd e d.

Definition latch_state γl (counter: nat): iProp :=
  own γl (◯ (0, Some (match counter with
        0 => Cinr ε
      | _ => Cinl (Excl (Pos.of_nat counter))
                      end))).

Theorem newLatch_spec (c: Z):
  {{{ inv_heap_inv }}}
    newLatch array_interface #c
  {{{ γl γa γtq γe γd s, RET s; is_latch γl γa γtq γe γd s ∗
                                latch_state γl (if decide (0 ≤ c)%Z then Z.to_nat c else 0)
  }}}.
Proof.
  iIntros (Φ) "#HHeap HΦ".
  remember (if decide (0 ≤ c)%Z then Z.to_nat c else 0) as n.
  destruct n as [|n'].
  {
    iMod (own_alloc (● (0, Some (Cinr None)) ⋅ ◯ (0, Some (Cinr None))))
      as (γl) "[H● H◯]".
    by apply auth_both_valid=> //.
    wp_lam. wp_bind (newThreadQueue _ _).
    iApply (newThreadQueue_spec with "HHeap").
    iIntros (γa γtq γe γd e d) "!> [#HTq HThreadState]".
    wp_alloc pw as "Hpw". wp_alloc p as "Hp". rewrite -wp_fupd. wp_pures.
    iMod (inv_alloc NLatch _ (∃ n w, latch_invariant γl γtq p pw n w) with "[-HΦ H◯]")
      as "#HInv".
    { iExists 0, 0. simpl. iLeft. iFrame "Hpw HThreadState". iRight. iFrame.
      iSplitR; first done. iExists _. iFrame. iPureIntro.
      destruct (decide (0 ≤ c)%Z); lia. }
    iApply "HΦ". iSplitR.
    { iExists _, _, _, _. iSplitR; first done. by iFrame "HInv HTq". }
    rewrite /latch_state. by iFrame.
  }
  remember (S n') as n eqn:Hn'.
  iMod (own_alloc (● (0, Some (Cinl (Excl (Pos.of_nat n)))) ⋅
                   ◯ (0, Some (Cinl (Excl (Pos.of_nat n))))))
    as (γl) "[H● H◯]".
  by apply auth_both_valid=> //.
  wp_lam. wp_bind (newThreadQueue _ _).
  iApply (newThreadQueue_spec with "HHeap").
  iIntros (γa γtq γe γd e d) "!> [#HTq HThreadState]".
  wp_alloc pw as "Hpw". wp_alloc p as "Hp". rewrite -wp_fupd. wp_pures.
  iMod (inv_alloc NLatch _ (∃ n w, latch_invariant γl γtq p pw n w) with "[-HΦ H◯]")
    as "#HInv".
  { iExists n, 0. simpl. iLeft. iFrame "Hpw HThreadState". iLeft. iFrame.
    destruct (decide (0 ≤ c)%Z); last lia. rewrite Heqn.
    rewrite Z2Nat.id; last lia. iFrame. iPureIntro. lia. }
  iApply "HΦ". iSplitR.
  { iExists _, _, _, _. iSplitR; first done. by iFrame "HInv HTq". }
  rewrite /latch_state. by destruct n; first lia.
Qed.

Lemma await_spec γl γa γtq γe γd s:
  {{{ is_latch γl γa γtq γe γd s }}}
    await array_interface s @ ⊤
  {{{ γf v, RET v;
      is_latch_future γl γtq γa γf v ∗
      thread_queue_future_cancellation_permit γf ∗
      latch_waiter_permit γl γf }}}.
Proof.
  iIntros (Φ) "#HLatch HΦ". wp_lam. rewrite /is_latch.
  iDestruct "HLatch" as (e d p pw ->) "[HInv HTq]".
  wp_pures. wp_bind (!_)%E.
  iInv "HInv" as (n w) "HLatchInv" "HClose".
  iDestruct "HLatchInv" as
      "[(Hpw & HTqState & [(>% & H● & Hp)|(>-> & H● & Hp)])|
        (Hpw & HTqState & >-> & H● & Hp)]".
  - wp_load. iMod ("HClose" with "[-HΦ]") as "_".
    { iExists _, _. iLeft. iFrame "Hpw HTqState". iLeft. by iFrame. }
    iModIntro. wp_pures. rewrite bool_decide_false; last lia. clear. wp_pures.
    wp_lam. wp_bind (FAA _ _).
    iInv "HInv" as (n w) "HLatchInv" "HClose".
    iDestruct "HLatchInv" as "[(Hpw & HTqState & HRest)|
      (Hpw & HTqState & >-> & H● & Hp)]".
    * wp_faa.
      iMod (thread_queue_append' with "HTq [] HTqState")
        as "[HState HSus]"=> /=; [by solve_ndisj|done|].
      iAssert (
          |==>
          latch_waiter_registered γl ∗
          (⌜n > 0⌝ ∧ own γl (● (S w, Some (Cinl (Excl (Pos.of_nat n))))) ∗ p ↦ #n
           ∨ ⌜n = 0⌝ ∧ own γl (● (S w, Some (Cinr None))) ∗ (∃ n' : Z, ⌜(n' ≤ 0)%Z⌝ ∧ p ↦ #n'))
      )%I with "[HRest]" as ">[HToken HRest]".
      {
        iDestruct "HRest" as "[(H1 & H● & H2)|(H1 & H● & H2)]".
        2: iMod (own_update with "H●") as "[H● $]"; last by iRight; iFrame.
        1: iMod (own_update with "H●") as "[H● $]"; last by iLeft; iFrame.
        all: apply auth_update_alloc, prod_local_update_1, nat_local_update.
        all: replace ε with 0 by done; lia.
      }
      iMod ("HClose" with "[-HSus HΦ HToken]") as "_".
      { iExists _, _. iLeft. iFrame.
        replace ((w * 2)%nat + 2)%Z with (Z.of_nat (S w * 2)) by lia.
        by iFrame. }
      iModIntro. wp_pures. wp_lam. wp_pures. rewrite bool_decide_false.
      2: { case. rewrite Nat2Z.inj_mul Z.rem_mul; lia. }
      wp_pures. wp_apply (suspend_spec with "[$]")=>/=.
      iIntros (v) "[(_ & _ & %)|Hv]"; first done.
      iDestruct "Hv" as (γf v' ->) "[HFuture HCancPermit]".
      wp_pures. iApply "HΦ". iFrame.
    * wp_faa.
      iAssert (|==> own γl (● (S w, Some (Cinr _))) ∗
                    (latch_broken γl ∗ latch_waiter_registered γl))%I
        with "[H●]" as ">[H● [H◯ HToken]]".
      { iMod (own_update with "H●") as "[$ [$ $]]"; last done.
        apply auth_update_alloc=> /=. apply prod_local_update=> /=.
        - apply nat_local_update. replace ε with 0 by done.
          replace (0 ⋅ 1) with 1 by done. lia.
        - rewrite cmra_comm. apply core_id_local_update.
          apply _. apply Some_included. right. apply Cinr_included.
          apply ucmra_unit_least.
      }
      iMod ("HClose" with "[-HΦ H◯ HToken]") as "_".
      { iExists 0, (S w). iRight. iFrame. iSplitL; last done.
        by replace (Z.of_nat (S w * 2 + 1)) with ((w * 2 + 1)%nat + 2)%Z by lia. }
      iModIntro. wp_pures. wp_lam. wp_pures. rewrite bool_decide_true.
      2: { congr LitV.
        rewrite Nat.add_comm Nat2Z.inj_add Nat2Z.inj_mul Z.rem_add //; lia. }
      wp_pures.
      iApply (fillThreadQueueFuture_spec with "[H◯]").
      2: by iIntros "!>" (γf v') "(H & H' & H'')"; iApply "HΦ"; iFrame.
      rewrite /V'. iExists _. simpl. iFrame. done.
  - iDestruct "Hp" as (n') "[>% Hp]". wp_load.
    iAssert (|==> own γl (● _) ∗ latch_broken γl)%I with "[H●]" as ">[H● H◯]".
    { iMod (own_update with "H●") as "[$ $]"; last done.
      apply auth_update_core_id. apply _. apply prod_included=> /=. split.
      by apply nat_included; lia.
      apply Some_included. right. apply Cinr_included. apply ucmra_unit_least. }
    iMod ("HClose" with "[-HΦ H◯]") as "_".
    { iExists _, _. iLeft. iFrame "Hpw HTqState". iRight. iFrame.
      iSplitR; first done. iExists n'. iFrame. done. }
    iModIntro. wp_pures. rewrite bool_decide_true; last lia. wp_pures.
    iApply (fillThreadQueueFuture_spec with "[H◯]").
    2: { iIntros "!>" (γf v') "(H & H' & H'')"; iApply "HΦ"; iFrame.
         by iRight; iExists _. }
    rewrite /V'. iExists _. simpl. iFrame. done.
  - iDestruct "Hp" as (n') "[>% Hp]". wp_load.
    iAssert (|==> own γl (● _) ∗ latch_broken γl)%I with "[H●]" as ">[H● H◯]".
    { iMod (own_update with "H●") as "[$ $]"; last done.
      apply auth_update_core_id. apply _. apply prod_included=> /=. split.
      by apply nat_included; lia.
      apply Some_included. right. apply Cinr_included. apply ucmra_unit_least. }
    iMod ("HClose" with "[-HΦ H◯]") as "_".
    { iExists _, _. iRight. iFrame "Hpw HTqState". iFrame.
      iSplitR; first done. iExists n'. iFrame. done. }
    iModIntro. wp_pures. rewrite bool_decide_true; last lia. wp_pures.
    iApply (fillThreadQueueFuture_spec with "[H◯]").
    2: {
      iIntros "!>" (γf v') "(H & H' & H'')"; iApply "HΦ"; iFrame.
      iRight. by iExists _. }
    rewrite /V'. iExists _. simpl. iFrame. done.
Qed.

Lemma excl_included {A: ofeT} (a b: A): Excl a ≼ Excl b -> a ≡ b.
Proof. intros [x y]. destruct x; inversion_clear y. Qed.

Lemma getCount_spec γl γa γtq γe γd s:
  is_latch γl γa γtq γe γd s -∗
  <<< ∀ (n: nat), latch_state γl n >>>
    getCount s @ ⊤ ∖ ↑NLatch
  <<< latch_state γl n, RET #n >>>.
Proof.
  iIntros "#HLatch" (Φ) "AU". wp_lam.
  iDestruct "HLatch" as (e d p pw ->) "[HInv HTq]". wp_pures. wp_bind (!_)%E.
  iInv "HInv" as (n' w) "HOpen" "HInvClose".
  iMod "AU" as (n) "[HState [_ HClose]]".
  iDestruct "HOpen" as
      "[(Hpw & HTqState & [(>% & H● & Hp)|(>-> & H● & Hp)])|
        (Hpw & HTqState & >-> & H● & Hp)]".
  - wp_load.
    iAssert (⌜n' = n⌝)%I as %->.
    { iDestruct (own_valid_2 with "H● HState")
        as %[[_ HValid%Some_included]%prod_included _]%auth_both_valid.
      destruct n as [|n].
      { exfalso. move: HValid. case. by move=> HContra; inversion HContra.
        rewrite csum_included. case; first done.
        case; intros (? & ? & ? & ? & ?)=> //. }
      iPureIntro. move: HValid. rewrite Cinl_included.
      case; move=> HValid; [apply Cinl_inj in HValid; inversion HValid; subst|
                           apply excl_included in HValid].
      all: apply Nat2Pos.inj; [lia|lia|done].
    }
    iMod ("HClose" with "HState") as "HΦ". iModIntro.
    iMod ("HInvClose" with "[-HΦ]") as "_".
    { iExists _, _. iLeft. iFrame "Hpw HTqState". iLeft. by iFrame. }
    iModIntro. wp_pures. rewrite bool_decide_false; last lia. by wp_pures.
  - iDestruct "Hp" as (n'') "[>% Hp]".
    wp_load.
    iAssert (⌜n = 0⌝)%I as %->.
    { iDestruct (own_valid_2 with "H● HState")
        as %[[_ HValid%Some_included]%prod_included _]%auth_both_valid.
      destruct n as [|n]; first done.
      { exfalso. move: HValid. case. by move=> HContra; inversion HContra.
        rewrite csum_included. case; first done.
        case; intros (? & ? & ? & ? & ?)=> //. }
    }
    iMod ("HClose" with "HState") as "HΦ". iModIntro.
    iMod ("HInvClose" with "[-HΦ]") as "_".
    { iExists _, _. iLeft. iFrame "Hpw HTqState". iRight. iFrame.
      iSplitR; first done. iExists _. iSplitR; last iFrame. done. }
    iModIntro. wp_pures. rewrite bool_decide_true; last lia.
    by wp_pures.
  - iDestruct "Hp" as (n'') "[>% Hp]".
    wp_load.
    iAssert (⌜n = 0⌝)%I as %->.
    { iDestruct (own_valid_2 with "H● HState")
        as %[[_ HValid%Some_included]%prod_included _]%auth_both_valid.
      destruct n as [|n]; first done.
      { exfalso. move: HValid. case. by move=> HContra; inversion HContra.
        rewrite csum_included. case; first done.
        case; intros (? & ? & ? & ? & ?)=> //. }
    }
    iMod ("HClose" with "HState") as "HΦ". iModIntro.
    iMod ("HInvClose" with "[-HΦ]") as "_".
    { iExists _, _. iRight. iFrame.
      iSplitR; first done. iExists _. iSplitR; last iFrame. done. }
    iModIntro. wp_pures. rewrite bool_decide_true; last lia.
    by wp_pures.
Qed.

Lemma resumeWaiters_spec γl γa γtq γe γd s:
  {{{ is_latch γl γa γtq γe γd s ∗ latch_broken γl }}}
    resumeWaiters array_interface s
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "[#HLatch #HBroken] HΦ". wp_lam.
  iDestruct "HLatch" as (e d p pw ->) "[HInv HTq]". wp_pures.
  wp_lam. wp_pures.
  iLöb as "IH".
  wp_bind (!_)%E.
  iInv "HInv" as (n w) "HLatchInv" "HClose".
  iDestruct "HLatchInv" as
      "[(Hpw & HTqState & HRest)|
        (Hpw & HTqState & >-> & H● & Hp)]".
  all: wp_load.
  - iMod ("HClose" with "[-HΦ]") as "_".
    { iExists _, _. iLeft. iFrame "Hpw HTqState". by iFrame. }
    iModIntro. wp_pures. wp_lam. wp_pures. rewrite bool_decide_false.
    2: { case. rewrite Nat2Z.inj_mul Z.rem_mul; lia. }
    wp_pures. wp_lam. wp_pures. wp_bind (CmpXchg _ _ _). clear n.
    iInv "HInv" as (n w') "HLatchInv" "HClose".
    iDestruct "HLatchInv" as
        "[(Hpw & HTqState & HRest)|(Hpw & HTqState & >-> & H● & Hp)]".
    2: { wp_cmpxchg_fail. case; lia.
         iMod ("HClose" with "[-HΦ]") as "_".
         { iExists _, _. iRight. by iFrame. }
         iModIntro. wp_pures. wp_lam. wp_pures. by iApply "IH". }
    destruct (decide (w = w')).
    2: { wp_cmpxchg_fail. case; lia.
         iMod ("HClose" with "[-HΦ]") as "_".
         { iExists _, _. iLeft. by iFrame. }
         iModIntro. wp_pures. wp_lam. wp_pures. by iApply "IH". }
    wp_cmpxchg_suc. subst w'.
    iAssert (|={⊤ ∖ ↑NLatch}=> thread_queue_state γtq 0 ∗
            [∗] replicate w (awakening_permit γtq))%I
      with "[HTqState]" as ">[HState HAwaks]".
    {
      iClear "IH". clear. iInduction (w) as [|w] "IH"=>/=. by iFrame.
      iMod (thread_queue_register_for_dequeue' with
                "HTq [$] [$]") as "[HState $]". by solve_ndisj.
      lia. rewrite /= Nat.sub_0_r.
      iApply ("IH" with "HState").
    }
    iDestruct "HRest" as "[(_ & HContra & _)|(-> & H● & Hp)]".
    { iDestruct (own_valid_2 with "HContra HBroken")
        as %[[_ HValid]%prod_included _]%auth_both_valid.
      exfalso. move: HValid. rewrite Some_included. case.
      by intros HValid; inversion HValid.
      rewrite csum_included. case; first done.
      case; by intros (? & ? & ? & ? & ?). }
    iAssert (|==> own γl _ ∗ latch_closed γl)%I with "[H●]" as ">[H● H◯]".
    2: iMod ("HClose" with "[-HΦ H◯ HAwaks]") as "_".
    2: {
      iExists _, w. iRight. iFrame "HState". iSplitL "Hpw".
      by rewrite Nat2Z.inj_add.
      iSplitR; first done. iFrame.
    }
    { iMod (own_update with "H●") as "[$ $]"; last done.
      apply auth_update_alloc, prod_local_update_2, option_local_update'''=> //. }
    iModIntro. wp_pures. replace 2%Z with (Z.of_nat 2) by lia.
    rewrite quot_of_nat Nat.div_mul; last lia.
    wp_apply (forRange_resource_map
                (fun _ => awakening_permit γtq) (fun _ => True)%I
             with "[] [HAwaks]").
    + iIntros (i Ψ) "!> HAwak HΨ". wp_pures. wp_lam.
      wp_apply (resumeLatch_spec with "[$]"). iIntros (_).
      by iApply "HΨ".
    + by rewrite -big_sepL_replicate seq_length.
    + iIntros (?) "_". wp_pures. by iApply "HΦ".
  - iMod ("HClose" with "[-HΦ]") as "_".
    { iExists _, _. iRight. by iFrame. }
    iModIntro. wp_pures. wp_lam. wp_pures. rewrite bool_decide_true.
    2: { congr LitV.
         rewrite Nat.add_comm Nat2Z.inj_add Nat2Z.inj_mul Z.rem_add //; lia. }
    wp_pures. by iApply "HΦ".
Qed.

Lemma countDown_spec γl γa γtq γe γd s:
  is_latch γl γa γtq γe γd s -∗
  <<< ∀ n, latch_state γl n >>>
    countDown array_interface s @ ⊤ ∖ ↑NLatch
  <<< if decide (2 ≤ n)%nat then latch_state γl (n - 1)
      else latch_state γl 0 ∗ latch_broken γl,
      RET #() >>>.
Proof.
  iIntros "#HLatch" (Φ) "AU". wp_lam.
  iDestruct "HLatch" as (e d p pw ->) "[HInv HTq]". wp_pures. wp_bind (FAA _ _).
  iInv "HInv" as (n' w) "HOpen" "HInvClose".
  iMod "AU" as (n) "[HState [_ HClose]]".
  iDestruct "HOpen" as
      "[(Hpw & HTqState & [(>% & H● & Hp)|(>-> & H● & Hp)])|
        (Hpw & HTqState & >-> & H● & Hp)]".
  - wp_faa.
    iAssert (⌜n' = n⌝)%I as %->.
    { iDestruct (own_valid_2 with "H● HState")
        as %[[_ HValid%Some_included]%prod_included _]%auth_both_valid.
      destruct n as [|n].
      { exfalso. move: HValid. case. by move=> HContra; inversion HContra.
        rewrite csum_included. case; first done.
        case; intros (? & ? & ? & ? & ?)=> //. }
      iPureIntro. move: HValid. rewrite Cinl_included.
      case; move=> HValid; [apply Cinl_inj in HValid; inversion HValid; subst|
                           apply excl_included in HValid].
      all: apply Nat2Pos.inj; [lia|lia|done].
    }
    destruct (decide (2 ≤ n)).
    * rewrite /latch_state. destruct n as [|[|rn]]; [lia | lia |]. simpl.
      iAssert (|==> own γl (● (w, Some (Cinl (Excl (Pos.of_nat (S rn))))))
                    ∗ own γl (◯ (0, Some (Cinl (Excl (Pos.of_nat (S rn)))))))%I
              with "[H● HState]" as ">[H● HState]".
      { iDestruct (own_update_2 with "H● HState") as ">[$ $]"; last done.
        apply auth_update, prod_local_update_2, option_local_update, csum_local_update_l=> /=.
        by apply exclusive_local_update. }
      iMod ("HClose" with "HState") as "HΦ". iModIntro.
      iMod ("HInvClose" with "[-HΦ]") as "_".
      { iExists _, _. iLeft. iFrame "Hpw HTqState". iLeft. iFrame "H●".
        iSplitR; first by iPureIntro; lia.
        by replace (Z.of_nat (S rn)) with ((2 + rn)%nat + -1)%Z by lia. }
      iModIntro. wp_pures. rewrite bool_decide_false; last by lia. by wp_pures.
    * rewrite /latch_state. destruct n as [|[|]]; last lia.
      { iDestruct (own_valid_2 with "H● HState")
          as %[[_ HValid%Some_included]%prod_included _]%auth_both_valid. exfalso.
        move: HValid; case=> HValid. by inversion HValid.
        move: HValid. rewrite csum_included.
        case; first done. case; intros (? & ? & ? & ? & ?)=> //. }
      iAssert (|==> own γl (● (w, Some (Cinr ε))) ∗ own γl (◯ (0, Some (Cinr ε))))%I
              with "[H● HState]" as ">[H● #HState]".
      { iMod (own_update_2 with "H● HState") as "[$ $]"; last done.
        apply auth_update, prod_local_update_2.
        etransitivity. by apply delete_option_local_update, _.
        apply alloc_option_local_update. done. }
      iMod ("HClose" with "[$]") as "HΦ". iModIntro.
      iMod ("HInvClose" with "[-HΦ]") as "_".
      { iExists 0, _. iLeft. iFrame "Hpw HTqState". iRight. iFrame.
        iSplitR; first done. iExists 0. by iFrame. }
      iModIntro. wp_pures.
      wp_apply resumeWaiters_spec.
      { iFrame "HState". iExists _, _, _, _. iSplitR; first done.
        iFrame "HInv HTq". }
      by iIntros "_".
  - iDestruct "Hp" as (n') "[>% Hp]". wp_faa.
    destruct n=>/=.
    2: {
      iDestruct (own_valid_2 with "H● HState")
        as %[[_ HValid%Some_included]%prod_included _]%auth_both_valid.
      exfalso. move: HValid. case; first move=> HValid.
      by inversion HValid.
      rewrite csum_included. case; first done.
      case; by intros (? & ? & ? & ? & ?).
    }
    iDestruct "HState" as "#HState". iMod ("HClose" with "[$]") as "HΦ".
    iModIntro. iMod ("HInvClose" with "[-HΦ]") as "_".
    { iExists 0, _. iLeft. iFrame "Hpw HTqState". iRight. iFrame.
      iSplitR; first done. iExists _. iFrame. iPureIntro. lia. }
    iModIntro. wp_pures. rewrite bool_decide_true; last lia. wp_pures.
    wp_apply resumeWaiters_spec.
    { iFrame "HState". iExists _, _, _, _. iSplitR; first done.
      iFrame "HInv HTq". }
    by iIntros "_".
  - iDestruct "Hp" as (n') "[>% Hp]". wp_faa.
    destruct n=>/=.
    2: {
      iDestruct (own_valid_2 with "H● HState")
        as %[[_ HValid%Some_included]%prod_included _]%auth_both_valid.
      exfalso. move: HValid. case; first move=> HValid.
      by inversion HValid.
      rewrite csum_included. case; first done.
      case; by intros (? & ? & ? & ? & ?).
    }
    iDestruct "HState" as "#HState". iMod ("HClose" with "[$]") as "HΦ".
    iModIntro. iMod ("HInvClose" with "[-HΦ]") as "_".
    { iExists 0, _. iRight. iFrame. iSplitR; first done. iExists _. iFrame.
      iPureIntro. lia. }
    iModIntro. wp_pures. rewrite bool_decide_true; last lia. wp_pures.
    wp_apply resumeWaiters_spec.
    { iFrame "HState". iExists _, _, _, _. iSplitR; first done.
      iFrame "HInv HTq". }
    by iIntros "_".
Qed.

Lemma removeWaiter_local_update γl w r:
  own γl (● (w, r)) -∗ latch_waiter_registered γl ==∗
  own γl (● (w - 1, r)).
Proof.
  iIntros "H● H◯". iMod (own_update_2 with "H● H◯") as "$"; last done.
  apply auth_update_dealloc, prod_local_update_1.
  apply local_update_total_valid=> _ _. rewrite nat_included. move=> Hw.
  apply nat_local_update. replace ε with 0 by done. lia.
Qed.

Theorem cancelLatchFuture_spec γl γa γtq γe γd s γf f:
  is_latch γl γa γtq γe γd s -∗
  is_latch_future γl γtq γa γf f -∗
  <<< ▷ thread_queue_future_cancellation_permit γf ∗
      latch_waiter_permit γl γf >>>
    cancelLatchFuture array_interface s f @ ⊤ ∖ ↑NFuture ∖ ↑N
  <<< ∃ (r: bool),
      if r then future_is_cancelled γf
      else (∃ v, ▷ future_is_completed γf v) ∗
           thread_queue_future_cancellation_permit γf ∗
           latch_waiter_permit γl γf, RET #r >>>.
Proof.
  iIntros "#HLatch #HFuture" (Φ) "AU".
  iDestruct "HLatch" as (e d p pw ->) "[HInv HTq]". wp_lam. wp_pures. wp_lam.
  wp_pures. awp_apply (try_cancel_thread_queue_future with "HTq HFuture");
              first by solve_ndisj.
  iApply (aacc_aupd_commit with "AU"). by solve_ndisj.
  iIntros "[HCancPermit HWaiter]". iAaccIntro with "HCancPermit".
  by iIntros "$ !>"; iFrame; iIntros "$ !>".
  iIntros (r) "Hr". iExists r. destruct r.
  2: { iDestruct "Hr" as "[$ $]". iFrame. iIntros "!> HΦ !>". by wp_pures. }
  iDestruct "Hr" as "[#HFutureCancelled Hr]". iFrame "HFutureCancelled".
  rewrite /is_latch_future /is_thread_queue_future.
  iDestruct "Hr" as (i f' s ->) "Hr"=> /=.
  iDestruct "Hr" as "(#H↦~ & #HTh & HToken)". iIntros "!> HΦ !>". wp_pures.
  wp_lam. wp_pures. wp_apply derefCellPointer_spec.
  by iDestruct "HTq" as "(_ & $ & _)". iIntros (ℓ) "#H↦". wp_pures. wp_lam.
  iDestruct "HWaiter" as "[HWaiter|HContra]".
  2: {
    iDestruct "HContra" as (?) "HContra".
    iDestruct (future_is_completed_not_cancelled
                 with "HContra HFutureCancelled") as %[].
  }
  iLöb as "IHCancAllowed".
  wp_bind (FAA _ _).
  iInv "HInv" as (n w) "HOpen" "HInvClose".
  iDestruct "HOpen" as
      "[(Hpw & HTqState & HRest)|(Hpw & HTqState & >-> & H● & Hp)]".
  - wp_faa.
    iAssert (⌜w > 0⌝)%I as %Hw.
    { iAssert (∃ x, own γl (● (w, x)))%I with "[HRest]" as (?) "H●".
      by iDestruct "HRest" as "[(_ & H● & _)|(_ & H● & _)]"; by iExists _.
      iDestruct (own_valid_2 with "H● HWaiter")
        as %[[HValid%nat_included _]%prod_included _]%auth_both_valid.
      iPureIntro. simpl in *. lia.
    }
    iMod (register_cancellation with "HTq HToken HTqState")
        as "[HCancToken HTqState]"; first by solve_ndisj.
    rewrite bool_decide_false; last lia.
    iDestruct "HTqState" as "(HTqState & HR & #HInhabited)".
    iAssert (|==> (⌜n > 0⌝ ∧ own γl (● (w - 1, Some (Cinl (Excl (Pos.of_nat n))))) ∗ p ↦ #n
     ∨ ⌜n = 0⌝ ∧ own γl (● (w - 1, Some (Cinr None))) ∗ (∃ n' : Z, ⌜(n' ≤ 0)%Z⌝ ∧ p ↦ #n')))%I
                  with "[HRest HWaiter]" as ">HRest".
    {
      iDestruct "HRest" as "[(H1 & H● & H2)|(H1 & H● & H2)]";
        [iLeft|iRight]; iFrame "H1 H2".
      all: by iMod (removeWaiter_local_update with "H● HWaiter") as "$".
    }
    iMod ("HInvClose" with "[-HΦ HCancToken HR]") as "_".
    { iExists n, (w - 1). iLeft. iFrame "HTqState".
      replace (Z.of_nat ((w - 1) * 2)) with (Z.of_nat (w * 2) + (-2))%Z by lia.
      iFrame "Hpw". iFrame. }
    iModIntro. wp_pures. wp_lam. wp_pures. rewrite bool_decide_false.
    2: { case. rewrite Nat2Z.inj_mul Z.rem_mul; lia. }
    wp_pures. wp_bind (getAndSet.getAndSet _ _).
    awp_apply (markCancelled_spec with "HTq HInhabited H↦ HCancToken HTh")
              without "HΦ HR".
    iAaccIntro with "[//]"; first done. iIntros (v) "Hv"=>/=.
    iIntros "!> (HΦ & HCancHandle)". wp_pures.
    iAssert (▷ cell_cancellation_handle _ _ _ _ _ _)%I
            with "[HCancHandle]" as "HCancHandle"; first done.
    awp_apply (cancelCell_spec with "[] H↦~") without "Hv HΦ".
    by iDestruct "HTq" as "(_ & $ & _)".
    iAaccIntro with "HCancHandle". by iIntros "$".
    iIntros "#HCancelled !> [Hv HΦ]". wp_pures.
    iDestruct "Hv" as "[[-> _]|Hv]"; first by wp_pures.
    iDestruct "Hv" as (x ->) "(#HInhabited' & HAwak & %)"; simplify_eq.
    wp_pures. wp_apply (resumeLatch_spec with "[$]").
    iIntros "_". wp_pures. iApply "HΦ".
  - wp_faa.
    iAssert (⌜w > 0⌝)%I as %Hw.
    { iDestruct (own_valid_2 with "H● HWaiter")
        as %[[HValid%nat_included _]%prod_included _]%auth_both_valid.
      iPureIntro. simpl in *. lia. }
    iMod (register_cancellation with "HTq HToken HTqState")
        as "[HCancToken HState]"; first by solve_ndisj.
    iDestruct "HState" as "(HTqState & HR & #HInhabited)".
    iMod (removeWaiter_local_update with "H● HWaiter") as "H●".
    iMod ("HInvClose" with "[-HΦ HCancToken HR]") as "_".
    { iExists 0, (w - 1). iRight. iFrame.
      replace ((w * 2 + 1)%nat + -2)%Z with (Z.of_nat ((w - 1) * 2 + 1)) by lia.
      by iFrame.
    }
    iModIntro. wp_pures. wp_lam. wp_pures.
    rewrite bool_decide_true.
    2: { congr LitV.
         rewrite Nat.add_comm Nat2Z.inj_add Nat2Z.inj_mul Z.rem_add //; lia. }
    wp_pures. wp_bind (getAndSet.getAndSet _ _).
    awp_apply (markRefused_spec with "HTq HInhabited H↦ HCancToken HTh [//]")
              without "HΦ HR".
    iAaccIntro with "[//]"; first done. iIntros (v) "Hv"=>/=.
    iIntros "!> [HΦ HR]". iDestruct "Hv" as "[[-> _]|Hv]"; first by wp_pures.
    iDestruct "Hv" as (? ->) "[_ >%]". simplify_eq. wp_pures.
    iApply "HΦ".
Qed.

End proof.
