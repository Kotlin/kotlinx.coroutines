From iris.heap_lang Require Import notation.

Require Import SegmentQueue.lib.thread_queue.thread_queue.

Section impl.

Variable segment_size : positive.

Definition new_semaphore : val :=
  λ: "n", "availablePermits" <- ref "n" ;;
          ("availablePermits", new_thread_queue segment_size #()).

Definition cancellation_handler : val :=
  λ: "availablePermits" "head" "deqIdx" "canceller",
  let: "p" := FAA "availablePermits" #1
  in if: #0 ≤ "p" then #() else
  if: "canceller" #() then #()
  else resume segment_size "head" "deqIdx".

Definition acquire_semaphore : val :=
  λ: "cancHandle" "threadHandle" "availablePermits" "tail" "enqIdx" "head" "deqIdx",
  let: "p" := FAA "availablePermits"  #(-1)
  in if: #0 < "p" then #()
  else suspend segment_size
               (cancellation_handler "availablePermits" "head" "deqIdx")
               "threadHandle" "tail" "enqIdx".

Definition release_semaphore : val :=
  λ: "availablePermits" "head" "deqIdx",
  let: "p" := FAA "availablePermits" #1
  in if: #0 ≤ "p" then #()
  else resume segment_size "head" "deqIdx".

End impl.

From iris.base_logic.lib Require Import invariants.
From iris.heap_lang Require Import proofmode.
From iris.algebra Require Import auth.
From iris.algebra Require Import list gset excl csum.
From iris.program_logic Require Import atomic.

Require Import SegmentQueue.lib.infinite_array.infinite_array_impl.
Require Import SegmentQueue.lib.infinite_array.iterator.

Section proof.

Notation algebra := (authR (prodUR (optionUR (exclR natO)) natUR)).

Class semaphoreG Σ := SemaphoreG { semaphore_inG :> inG Σ algebra }.
Definition semaphoreΣ : gFunctors := #[GFunctor algebra].
Instance subG_semaphoreΣ {Σ} : subG semaphoreΣ Σ -> semaphoreG Σ.
Proof. solve_inG. Qed.

Context `{iArrayG Σ} `{iteratorG Σ} `{heapG Σ} `{threadQueueG Σ} `{semaphoreG Σ} `{parkingG Σ}.
Variable (Nth: namespace) (N: namespace).
Variable (namespaces_disjoint : Nth ## N).
Notation iProp := (iProp Σ).

Variable (segment_size: positive).

Definition is_semaphore_inv (R : iProp) (γ: gname) (availablePermits: nat) (p: loc)
  (epℓ eℓ dpℓ dℓ: loc) (γa γtq γe γd: gname) :=
  (∃ (readyToCancel: nat) l deqFront,
  ([∗ list] _ ∈ seq 0 availablePermits, R) ∗
   own γ (● (Excl' availablePermits, readyToCancel)) ∗
   is_thread_queue (N .@ "tq") Nth segment_size True R γa γtq γe γd eℓ epℓ dℓ dpℓ l deqFront ∗
   let v := count_matching still_present (drop deqFront l) in
   p ↦ #(availablePermits - v + readyToCancel) ∗
   ⌜readyToCancel <= v ∧ (availablePermits = 0 ∨ v = readyToCancel)%nat⌝)%I.

Definition is_semaphore (R : iProp) (γ: gname) (p: loc)
           (epℓ eℓ dpℓ dℓ: loc) (γa γtq γe γd: gname) :=
  inv (N .@ "semaphore") (∃ availablePermits,
            is_semaphore_inv R γ availablePermits p epℓ eℓ dpℓ dℓ γa γtq γe γd)%I.

Definition semaphore_permits γ availablePermits :=
  own γ (◯ (Excl' availablePermits, ε)).

Theorem count_matching_find_index_Some A (P: A -> Prop) (H': forall x, Decision (P x)) l:
  count_matching P l > 0 -> is_Some (find_index P l).
Proof.
  induction l; simpl; first done.
  destruct (decide (P a)); first by eauto.
  destruct (find_index P l); by eauto.
Qed.

Theorem release_semaphore_spec R γ (p epℓ eℓ dpℓ dℓ: loc) γa γtq γe γd:
  is_semaphore R γ p epℓ eℓ dpℓ dℓ γa γtq γe γd -∗
  inv (N .@ "permits") (∃ a, semaphore_permits γ a) -∗
  {{{ R }}}
    (release_semaphore segment_size) #p #dpℓ #dℓ
  {{{ RET #(); True }}}.
Proof.
  iIntros "#HSemInv #HPermInv" (Φ) "!> HR HΦ". wp_lam. wp_pures.
  wp_bind (FAA _ _).
  iInv "HSemInv" as (availablePermits' readyToCancel l deqFront)
                      "(HPerms & >HAuth & HTq & Hp & >HPure)" "HInvClose".
  iDestruct "HPure" as %HPure.
  remember (count_matching _ _) as v.
  remember (availablePermits' - v + readyToCancel) as op.
  wp_faa.
  destruct (decide (0 <= op)).
  {
    iInv "HPermInv" as (availablePermits) ">HFrag" "HInvClose'".
    iDestruct (own_valid_2 with "HAuth HFrag") as
        %[[<-%Excl_included%leibniz_equiv _]%prod_included _]%auth_both_valid.
    iMod (own_update_2 with "HAuth HFrag") as "[HAuth HFrag]".
    {
      apply auth_update, prod_local_update_1, option_local_update.
      apply (exclusive_local_update _ (Excl (1 + availablePermits)%nat)).
      done.
    }
    repeat rewrite Nat.add_1_r.
    iMod ("HInvClose'" with "[HFrag]") as "_"; first by eauto.
    iMod ("HInvClose" with "[-HΦ]") as "_".
    {
      iExists _, _, _, _. simpl. iFrame "HAuth HTq". simpl.
      iFrame "HR".
      iSplitL "HPerms".
      {
        iApply (big_opL_forall' with "HPerms").
        by repeat rewrite seq_length.
        done.
      }
      iSplitL.
      {
        rewrite -Heqv Heqop.
        replace (S availablePermits - v + readyToCancel)
                with (availablePermits - v + readyToCancel + 1).
        done.
        lia.
      }
      iPureIntro.
      split; lia.
    }
    iModIntro. wp_pures. rewrite bool_decide_decide.
    destruct (decide (0 <= op)); try lia. wp_pures. by iApply "HΦ".
  }

  assert (v > 0) as HExistsNondequed by lia.
  move: HExistsNondequed. subst. move=> HExistsNondequed.

  apply count_matching_find_index_Some in HExistsNondequed.
  destruct HExistsNondequed as [? HFindIndex].

  iDestruct "HTq" as "(HInfArr & HListContents & HCancA & % & HRest)".
  iDestruct (cell_list_contents_register_for_dequeue
               with "HR HListContents") as ">[[HAwak #HDeqFront] [HListContents HCounts]]".
  by eauto.
  iDestruct "HCounts" as %HCounts.

  iMod ("HInvClose" with "[-HAwak HΦ]") as "_".
  {
    iExists _, _, _, _. iFrame "HListContents". iFrame.
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
    iSplitL.
    {
      rewrite HCounts.
      clear.
      remember (count_matching _ _) as v.
      replace (availablePermits' - S v + readyToCancel + 1)
              with (availablePermits' - v + readyToCancel) by lia.
      done.
    }
    iPureIntro.
    lia.
  }

  iModIntro. wp_pures. rewrite bool_decide_decide.
  rewrite decide_False; auto.
  wp_pures. wp_lam. wp_pures.

  awp_apply (try_deque_thread_spec (N .@ "tq") with "HAwak") without "HΦ".
  iInv "HSemInv" as (? ? ? deqFront') "(HPerms & >HAuth & HTq & HRest)".
  iAaccIntro with "HTq".
  {
    iIntros "HTq !>".
    iSplitL; last done.
    iExists _, _, _, _. iFrame.
  }
  iIntros (?) "[_ HState]".
  iDestruct "HState" as (i) "[HState|HState]".
  {
    iDestruct "HState" as "[(HEl & -> & HTq) HRend]".
    iDestruct "HEl" as %HEl.
    iSplitL.
    2: {
      iIntros "!> HΦ".
      wp_pures.
      by iApply "HΦ".
    }
    destruct (decide (i < deqFront')%nat).
    2: {
      iDestruct "HTq" as "(_ & (_ & >HResumerStage & _) & _)".
      rewrite big_sepL_forall.
      iSpecialize ("HResumerStage" $! (i - deqFront')%nat _ with "[]").
      {
        iPureIntro.
        rewrite lookup_drop.
        replace (deqFront' + (i - deqFront'))%nat with i by lia.
        rewrite list_lookup_alter.
        rewrite HEl. done.
      }
      simpl.
      iDestruct "HResumerStage" as %HContra.
      discriminate.
    }
    iExists _, _, _, _. iFrame "HPerms HAuth HTq".
    iDestruct "HRest" as "[Hp >%]".
    rewrite drop_alter //.
    iSplitL "Hp"; done.
  }

  iDestruct "HState" as (? ?) "[#[HIsThread HThreadLocs] [HState|HState]]".
  2: {
    iDestruct "HState" as "[HState (-> & HTq & #HRendAbandoned & HNoPerms)]".
    iSplitR "HNoPerms".
    by iExists _, _, _, _; iFrame.
    iIntros "!> HΦ". wp_pures.
    awp_apply (unpark_spec with "HIsThread") without "HΦ".
    iAaccIntro with "HNoPerms".
    by iIntros ">HNoPerms !>".
    iIntros "HPerms !> HΦ". wp_pures. by iApply "HΦ".
  }
  {
    iDestruct "HState" as (HEl ?) "(HTq & #HRendRes & HResTok)".
    iDestruct "HRest" as "[Hp >%]".
    subst.
    iSplitR "HResTok".
    {
      destruct (decide (i < deqFront')%nat).
      2: {
        iDestruct "HTq" as "(_ & (_ & >HResumerStage & _) & _)".
        rewrite big_sepL_forall.
        iSpecialize ("HResumerStage" $! (i - deqFront')%nat _ with "[]").
        {
          iPureIntro.
          rewrite lookup_drop.
          replace (deqFront' + (i - deqFront'))%nat with i by lia.
          rewrite list_lookup_alter.
          rewrite HEl. done.
        }
        simpl.
        iDestruct "HResumerStage" as %HContra.
        discriminate.
      }
      iExists _, _, _, _. iFrame "HTq HAuth".
      rewrite drop_alter //.
      by iFrame.
    }
    iIntros "!> HΦ". wp_pures.
    awp_apply (unpark_spec with "HIsThread") without "HΦ".

    iInv "HSemInv" as (? ? l' ?) "(HPerms & >HAuth & (HInfArr & HListContents & HRest') & HRest)".
    iDestruct "HListContents" as "(HLi1 & HLi2 & >HTqAuth & HLi4 & HLi5 & HCellResources)".

    iDestruct "HRendRes" as (? ?) "HRendRes".

    iDestruct (cell_list_contents_done_agree with "HTqAuth HRendRes")
              as %HEl'.

    iDestruct (cell_list_contents_ra_locs with "HTqAuth HThreadLocs")
              as %[? HEl''].
    simplify_eq.

    iDestruct (big_sepL_lookup_acc with "HCellResources") as "[HRes HRRsRestore]".
    done.
    simpl.
    iAssert (resumer_token γtq i -∗ resumer_token γtq i -∗ False)%I as "HNoResTok".
    {
      iIntros "HResTok HResTok'".
      iDestruct (own_valid_2 with "HResTok HResTok'") as %HH.
      rewrite -auth_frag_op in HH. exfalso. move: HH.
      rewrite auth_frag_valid pair_valid list_op_singletonM list_lookup_valid /=.
      intros [_ HValid]. specialize (HValid i). move: HValid.
      rewrite list_lookup_singletonM.
      intros HValid.
      destruct HValid as [[[_ []] _] _].
    }
    iDestruct "HRes" as (ℓ) "(HArrMapsto & HTH & HIsSus & HIsRes & HCancHandle &
                             HConds)".
    iDestruct "HConds" as "[[HInhTok [HNoPerms|>HResTok']]|
                           [Hℓ [HR [[_ >HResTok']|HNoPerms]]]]";
      try iDestruct ("HNoResTok" with "HResTok HResTok'") as %[].

    all: iAaccIntro with "HNoPerms".
    3: {
      iFrame "HResTok".
      iIntros ">HNoPerms !>". iExists _, _, _, _. iFrame.
      iApply ("HRRsRestore" with "[-]").
      iExists _. iFrame.
      iRight; iFrame.
    }
    {
      iFrame "HResTok".
      iIntros ">HNoPerms !>". iExists _, _, _, _. iFrame.
      iApply ("HRRsRestore" with "[-]").
      iExists _. iFrame.
    }

    {
      iIntros "HThPerms !>".
      iSplitL.
      2: iIntros "HΦ"; wp_pures; by iApply "HΦ".
      iExists _, _, _, _. iFrame.
      iApply ("HRRsRestore" with "[-]").
      iExists _. iFrame. iLeft. iFrame.
    }

    {
      iIntros "HThPerms !>".
      iSplitL.
      2: iIntros "HΦ"; wp_pures; by iApply "HΦ".
      iExists _, _, _, _. iFrame.
      iApply ("HRRsRestore" with "[-]").
      iExists _. iFrame. iRight. iFrame. iLeft. iFrame.
    }
  }

Qed.

End proof.
