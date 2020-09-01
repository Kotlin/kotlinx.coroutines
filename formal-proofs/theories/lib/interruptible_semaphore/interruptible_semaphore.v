Require Import SegmentQueue.lib.thread_queue.thread_queue.
From iris.heap_lang Require Import notation.

Section impl.

Variable segment_size : positive.

Definition new_semaphore : val :=
  λ: "n", (ref "n", new_thread_queue segment_size #()).

Definition cancellation_handler : val :=
  λ: "availablePermits" "head" "deqIdx" "canceller" <>,
  let: "p" := FAA "availablePermits" #1
  in if: #0 ≤ "p" then InjLV #() else
  if: "canceller" #() then InjLV #()
  else resume segment_size "head" "deqIdx" ;; InjLV #().

Definition acquire_semaphore : val :=
  λ: "cancHandle" "threadHandle" "availablePermits" "tail" "enqIdx" "head" "deqIdx",
  let: "p" := FAA "availablePermits"  #(-1)
  in if: #0 < "p" then InjRV #()
  else suspend segment_size
               (cancellation_handler "availablePermits" "head" "deqIdx")
               "cancHandle" "threadHandle" "tail" "enqIdx".

Definition release_semaphore : val :=
  λ: "availablePermits" "head" "deqIdx",
  let: "p" := FAA "availablePermits" #1
  in if: #0 ≤ "p" then #()
  else resume segment_size "head" "deqIdx".

End impl.

Require Import SegmentQueue.lib.infinite_array.infinite_array_impl.
Require Import SegmentQueue.lib.infinite_array.iterator.
Require Import SegmentQueue.lib.util.interruptibly.
Require Import SegmentQueue.lib.thread_queue.thread_queue_as_counter.
From SegmentQueue.util Require Import everything big_opL.

From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import auth.
From iris.algebra Require Import list gset excl csum.
From iris.program_logic Require Import atomic.
From iris.heap_lang Require Import proofmode.

Section proof.

Notation algebra := (authR (optionUR (exclR natO))).

Class semaphoreG Σ := SemaphoreG { semaphore_inG :> inG Σ algebra }.
Definition semaphoreΣ : gFunctors := #[GFunctor algebra].
Instance subG_semaphoreΣ {Σ} : subG semaphoreΣ Σ -> semaphoreG Σ.
Proof. solve_inG. Qed.

Context `{iArrayG Σ} `{iteratorG Σ} `{heapG Σ} `{threadQueueG Σ} `{semaphoreG Σ}
        `{parkingG Σ} `{interruptiblyG Σ}.
Variable (Nth: namespace) (N: namespace).
Variable (namespaces_disjoint : Nth ## N).
Notation iProp := (iProp Σ).

Variable (segment_size: positive).

Definition is_semaphore_inv (R : iProp) (γ: gname) (availablePermits: nat) (p: loc)
  (epℓ eℓ dpℓ dℓ: loc) (γa γtq γe γd: gname) :=
  (∃ v, ([∗ list] _ ∈ seq 0 availablePermits, R) ∗
   own γ (● (Excl' availablePermits)) ∗
   thread_queue_as_counter (N .@ "tq") Nth segment_size True R γa γtq γe γd eℓ epℓ dℓ dpℓ v ∗
   p ↦ #(availablePermits - v) ∗ ⌜(availablePermits = 0 ∨ v = 0)%nat⌝)%I.

Definition is_semaphore (R : iProp) (γ: gname) (p: loc)
           (epℓ eℓ dpℓ dℓ: loc) (γa γtq γe γd: gname) :=
  inv (N .@ "semaphore") (∃ availablePermits,
            is_semaphore_inv R γ availablePermits p epℓ eℓ dpℓ dℓ γa γtq γe γd)%I.

Definition semaphore_permits γ availablePermits :=
  own γ (◯ (Excl' availablePermits)).

Lemma new_semaphore_spec (n: nat) R:
  {{{ ([∗ list] x ∈ replicate n R, x) }}}
    new_semaphore segment_size #n
  {{{ p γ γa γtq γe γd eℓ epℓ dℓ dpℓ, RET (#p, ((#epℓ, #eℓ), (#dpℓ, #dℓ)));
      is_semaphore R γ p epℓ eℓ dpℓ dℓ γa γtq γe γd ∗
      semaphore_permits γ n
  }}}.
Proof.
  iIntros (Φ) "HRs HΦ".
  wp_lam.
  iMod (own_alloc (● (Excl' n%nat) ⋅ ◯ (Excl' n%nat))) as (γ) "[HAuth HFrag]".
  by apply auth_both_valid.
  wp_apply new_thread_queue_spec; first done.
  iIntros (γa γtq γe γd eℓ epℓ dℓ dpℓ) "HTq".
  wp_bind (ref _)%E.
  rewrite -wp_fupd.
  wp_alloc p as "Hp".
  iMod (inv_alloc (N .@ "semaphore") _
                  (∃ n, is_semaphore_inv R γ n p epℓ eℓ dpℓ dℓ γa γtq γe γd)%I
          with "[-HΦ HFrag]") as "#HInv".
  {
    iExists _.
    rewrite /is_semaphore_inv. iExists O. iFrame "HAuth".
    rewrite Z.sub_0_r. iFrame "Hp".
    iSplitL "HRs".
    2: {
      iSplitL; last by iPureIntro; right.
      iExists _, _. by iFrame.
    }
    iApply (big_sepL_forall_2 with "HRs").
    by rewrite replicate_length seq_length.
    intros ? ? ?. rewrite lookup_replicate. by intros _ [-> _].
  }
  iModIntro. wp_pures.
  iApply "HΦ".
  iFrame.
  rewrite /is_semaphore.
  done.
Qed.

Lemma resume_in_semaphore_spec R γ p epℓ eℓ dpℓ dℓ γa γtq γe γd:
  is_semaphore R γ p epℓ eℓ dpℓ dℓ γa γtq γe γd -∗
  inv (N.@"permits") (∃ a, semaphore_permits γ a) -∗
  {{{ awakening_permit γtq }}}
    (resume segment_size) #dpℓ #dℓ
  {{{ RET #(); True }}}.
Proof.
  iIntros "#HSemInv #HPermInv" (Φ) "!> HAwak HΦ". wp_lam. wp_pures.
  awp_apply (try_deque_thread_as_counter_spec (N .@ "tq") with "HAwak") without "HΦ".
  iInv "HSemInv" as (? ?) "(HPerms & >HAuth & HTq & HRest)".
  iAaccIntro with "HTq".
  {
    iIntros "HTq !>".
    iSplitL; last done.
    iExists _, _. iFrame.
  }
  iIntros (?) "(_ & HTq & HState)".
  iDestruct "HState" as "[->|HState]".
  {
    iSplitL; first by iExists _, _; iFrame.
    iIntros "!> HΦ". wp_pures. by iApply "HΦ".
  }

  iDestruct "HState" as (? ? ?) "(-> & #[HIsThread HThreadLocs] &
    [[HResTok #HRendRes]|HNoPerms])".
  2: {
    iSplitR "HNoPerms".
    by iExists _, _; iFrame.
    iIntros "!> HΦ". wp_pures.
    awp_apply (unpark_spec with "HIsThread") without "HΦ".
    iAaccIntro with "HNoPerms".
    by iIntros ">HNoPerms !>".
    iIntros "HPerms !> HΦ". wp_pures. by iApply "HΦ".
  }
  {
    iSplitR "HResTok"; first by iExists _, _; iFrame.
    iIntros "!> HΦ". wp_pures.

    awp_apply (thread_queue_as_counter_unpark_spec with
                   "HRendRes HIsThread HThreadLocs") without "HΦ".
    iInv "HSemInv" as (? ?) "(HPerms & >HAuth & HTq & HRest)".
    iCombine "HResTok" "HTq" as "HAacc".
    iAaccIntro with "HAacc".
    { iIntros "[$ HTq]". iExists _, _. by iFrame. }
    iIntros "HTq". iSplitL.
    by iExists _, _; iFrame.
    iIntros "!> HΦ". wp_pures. by iApply "HΦ".
  }
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
  iInv "HSemInv" as (availablePermits' v)
                      "(HPerms & >HAuth & HTq & Hp & >HPure)" "HInvClose".
  iDestruct "HPure" as %HPure.
  remember (availablePermits' - v)%Z as op.
  wp_faa.
  destruct (decide (0 <= op)%Z).
  {
    iInv "HPermInv" as (availablePermits) ">HFrag" "HInvClose'".
    iDestruct (own_valid_2 with "HAuth HFrag") as
        %[<-%Excl_included%leibniz_equiv _]%auth_both_valid.
    iMod (own_update_2 with "HAuth HFrag") as "[HAuth HFrag]".
    {
      apply auth_update, option_local_update.
      apply (exclusive_local_update _ (Excl (1 + availablePermits)%nat)).
      done.
    }
    iMod ("HInvClose'" with "[HFrag]") as "_"; first by eauto.
    iMod ("HInvClose" with "[-HΦ]") as "_".
    {
      iExists _, _. simpl. iFrame "HAuth HTq". simpl.
      iFrame "HR".
      iSplitL "HPerms".
      {
        iApply (big_sepL_forall_2 with "HPerms").
        by repeat rewrite seq_length.
        done.
      }
      iSplitL.
      {
        rewrite Heqop.
        replace (S availablePermits - v)%Z with (availablePermits - v + 1)%Z.
        done.
        lia.
      }
      iPureIntro. lia.
    }
    iModIntro. wp_pures. rewrite bool_decide_decide.
    destruct (decide (0 <= op)%Z); try lia. wp_pures. by iApply "HΦ".
  }

  iMod (thread_as_counter_register_for_dequeue with "HR HTq")
    as "[HAwak HTq]"; first by lia.

  iMod ("HInvClose" with "[-HAwak HΦ]") as "_".
  {
    iExists _, _. iFrame. subst.
    replace (availablePermits' - v + 1)%Z with (availablePermits' - (v - 1)%nat)%Z by lia.
    iFrame "Hp". iPureIntro. lia.
  }

  iModIntro. wp_pures. rewrite bool_decide_decide.
  rewrite decide_False; auto.
  wp_pures.

  by wp_apply (resume_in_semaphore_spec with "[$] [$] [$]").

Qed.

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
