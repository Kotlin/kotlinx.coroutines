From iris.heap_lang Require Import notation.

Require Import SegmentQueue.lib.thread_queue.thread_queue.

Section impl.

Variable segment_size : positive.

Definition new_semaphore : val :=
  λ: "n", "availablePermits" <- ref "n" ;;
          ("availablePermits", new_thread_queue segment_size #()).

Definition cancellation_handler : val :=
  λ: "availablePermits" "head" "deqIdx" "canceller" <>,
  let: "p" := FAA "availablePermits" #1
  in if: #0 ≤ "p" then #() else
  if: "canceller" #() then #()
  else resume segment_size "head" "deqIdx".

Definition acquire_semaphore : val :=
  λ: "cancHandle" "threadHandle" "availablePermits" "tail" "enqIdx" "head" "deqIdx",
  let: "p" := FAA "availablePermits"  #(-1)
  in if: #0 < "p" then #false
  else suspend segment_size
               (cancellation_handler "availablePermits" "head" "deqIdx")
               "cancHandle" "threadHandle" "tail" "enqIdx".

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
Require Import SegmentQueue.lib.util.interruptibly.

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
  (∃ l deqFront,
  ([∗ list] _ ∈ seq 0 availablePermits, R) ∗
   own γ (● (Excl' availablePermits)) ∗
   is_thread_queue (N .@ "tq") Nth segment_size True R γa γtq γe γd eℓ epℓ dℓ dpℓ l deqFront ∗
   let v := count_matching still_present (drop deqFront l) in
   p ↦ #(availablePermits - v) ∗ ⌜(availablePermits = 0 ∨ v = 0)%nat⌝)%I.

Definition is_semaphore (R : iProp) (γ: gname) (p: loc)
           (epℓ eℓ dpℓ dℓ: loc) (γa γtq γe γd: gname) :=
  inv (N .@ "semaphore") (∃ availablePermits,
            is_semaphore_inv R γ availablePermits p epℓ eℓ dpℓ dℓ γa γtq γe γd)%I.

Definition semaphore_permits γ availablePermits :=
  own γ (◯ (Excl' availablePermits)).

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
  iInv "HSemInv" as (availablePermits' l deqFront)
                      "(HPerms & >HAuth & HTq & Hp & >HPure)" "HInvClose".
  iDestruct "HPure" as %HPure.
  remember (count_matching _ _) as v.
  remember (availablePermits' - v) as op.
  wp_faa.
  destruct (decide (0 <= op)).
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
    repeat rewrite Nat.add_1_r.
    iMod ("HInvClose'" with "[HFrag]") as "_"; first by eauto.
    iMod ("HInvClose" with "[-HΦ]") as "_".
    {
      iExists _, _, _. simpl. iFrame "HAuth HTq". simpl.
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
        replace (S availablePermits - v) with (availablePermits - v + 1).
        done.
        lia.
      }
      iPureIntro.
      lia.
    }
    iModIntro. wp_pures. rewrite bool_decide_decide.
    destruct (decide (0 <= op)); try lia. wp_pures. by iApply "HΦ".
  }

  assert (v > 0) as HExistsNondequed by lia.
  move: HExistsNondequed. subst. move=> HExistsNondequed.

  apply count_matching_find_index_Some in HExistsNondequed.
  destruct HExistsNondequed as [? HFindIndex].

  iDestruct "HTq" as "(HInfArr & HListContents & % & HRest)".
  iDestruct (cell_list_contents_register_for_dequeue
               with "HR HListContents") as ">[[HAwak #HDeqFront] [HListContents HCounts]]".
  by eauto.
  iDestruct "HCounts" as %HCounts.

  iMod ("HInvClose" with "[-HAwak HΦ]") as "_".
  {
    iExists _, _, _. iFrame "HListContents". iFrame.
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
      replace (availablePermits' - S v + 1) with (availablePermits' - v) by lia.
      done.
    }
    iPureIntro.
    lia.
  }

  iModIntro. wp_pures. rewrite bool_decide_decide.
  rewrite decide_False; auto.
  wp_pures. wp_lam. wp_pures.

  awp_apply (try_deque_thread_spec (N .@ "tq") with "HAwak") without "HΦ".
  iInv "HSemInv" as (? ? deqFront') "(HPerms & >HAuth & HTq & HRest)".
  iAaccIntro with "HTq".
  {
    iIntros "HTq !>".
    iSplitL; last done.
    iExists _, _, _. iFrame.
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
    iExists _, _, _. iFrame "HPerms HAuth HTq".
    iDestruct "HRest" as "[Hp >%]".
    rewrite drop_alter //.
    iSplitL "Hp"; done.
  }

  iDestruct "HState" as (? ?) "[#[HIsThread HThreadLocs] [HState|HState]]".
  2: {
    iDestruct "HState" as "[HState (-> & HTq & HNoPerms)]".
    iSplitR "HNoPerms".
    by iExists _, _, _; iFrame.
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
      iExists _, _, _. iFrame "HTq HAuth".
      rewrite drop_alter //.
      by iFrame.
    }
    iIntros "!> HΦ". wp_pures.
    awp_apply (unpark_spec with "HIsThread") without "HΦ".

    iInv "HSemInv" as (? l' ?) "(HPerms & >HAuth & (HInfArr & HListContents & HRest') & HRest)".
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
      iIntros ">HNoPerms !>". iExists _, _, _. iFrame.
      iApply ("HRRsRestore" with "[-]").
      iExists _. iFrame.
      iRight; iFrame.
    }
    {
      iFrame "HResTok".
      iIntros ">HNoPerms !>". iExists _, _, _. iFrame.
      iApply ("HRRsRestore" with "[-]").
      iExists _. iFrame.
    }

    {
      iIntros "HThPerms !>".
      iSplitL.
      2: iIntros "HΦ"; wp_pures; by iApply "HΦ".
      iExists _, _, _. iFrame.
      iApply ("HRRsRestore" with "[-]").
      iExists _. iFrame. iLeft. iFrame.
    }

    {
      iIntros "HThPerms !>".
      iSplitL.
      2: iIntros "HΦ"; wp_pures; by iApply "HΦ".
      iExists _, _, _. iFrame.
      iApply ("HRRsRestore" with "[-]").
      iExists _. iFrame. iRight. iFrame. iLeft. iFrame.
    }
  }

Qed.

Theorem acquire_semaphore_spec Nint R γ (p epℓ eℓ dpℓ dℓ: loc) γa γtq γe γd
        γi cancHandle γth (threadHandle: loc):
  is_interrupt_handle Nint γi cancHandle -∗
  is_thread_handle Nth γth #threadHandle -∗
  is_semaphore R γ p epℓ eℓ dpℓ dℓ γa γtq γe γd -∗
  inv (N .@ "permits") (∃ a, semaphore_permits γ a) -∗
  {{{ thread_doesnt_have_permits γth }}}
    (acquire_semaphore segment_size) cancHandle #threadHandle #p #epℓ #eℓ #dpℓ #dℓ
  {{{ (v: bool), RET #v;
      ⌜v = false⌝ ∧ thread_doesnt_have_permits γth ∗ R ∨
      ⌜v = true⌝ ∧ interrupted γi
  }}}.
Proof.
  iIntros "#HIntHandle #HThreadHandle #HSemInv #HPermInv".
  iIntros (Φ) "!> HNoPerms HΦ".

  wp_lam. wp_pures. wp_bind (FAA _ _).
  iInv "HSemInv" as (availablePermits l deqFront)
                      "(HPerms & >HAuth & HTq & Hp & >HPure)" "HInvClose".
  wp_faa.
  iInv "HPermInv" as (?) ">HFrag" "HPermsClose".
  iDestruct (own_valid_2 with "HAuth HFrag") as
        %[->%Excl_included%leibniz_equiv _]%auth_both_valid.
  remember (availablePermits - _) as oldP.
  destruct (decide (0 < oldP)).
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
      iExists _, _, _.
      rewrite Nat.sub_0_r big_opL_irrelevant_element' seq_length.
      replace (oldP + -1) with
          (availablePermits - count_matching still_present (drop deqFront l)) by lia.
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
  iAssert (⌜deqFront <= length l⌝)%I as %HDeqFront.
  {
    iDestruct "HTq" as "(_ & _ & _ & HRest)".
    iDestruct "HRest" as (? ?) "(_ & _ & _ & _ & %)".
    iPureIntro.
    lia.
  }
  iMod (thread_queue_append with "[$] HTq") as "[[HIsSusp #HElExists] HTq]".
  iMod ("HPermsClose" with "[HFrag]") as "_"; first by eauto.
  iMod ("HInvClose" with "[-HIsSusp HNoPerms HΦ]") as "_".
  {
    iExists _, _, _. iFrame.
    rewrite drop_app_le.
    2: lia.
    rewrite count_matching_app. simpl.
    replace (- count_matching still_present (drop deqFront l) + -1) with
        (0%nat - (count_matching still_present (drop deqFront l) + 1)%nat) by lia.
    iFrame.
    iPureIntro. lia.
  }
  iModIntro. wp_pures. rewrite bool_decide_decide decide_False //. wp_pures.
  wp_lam. wp_pures. wp_lam. wp_pures.

  rewrite /is_semaphore.

  awp_apply (try_enque_thread_spec (N.@"tq") with "HThreadHandle HIsSusp HNoPerms")
            without "HΦ".
  iInv "HSemInv" as (? l' deqFront') "(HPerms & >HAuth & HTq & Hp & >HPure)".
  iAaccIntro with "HTq".
  {
    iIntros "HTq !>". iSplitL; last done.
    iExists _, _, _. iFrame.
  }
  iIntros (?) "HPures".
  iDestruct "HPures" as "[HTq|(-> & HTq & HNoPerms & HR)]".
  2: {
    iModIntro. iSplitR "HNoPerms HR".
    by iExists _, _, _; iFrame.
    iIntros "HΦ".
    wp_pures.
    iSpecialize ("HΦ" with "[-]").
    { iLeft. iFrame. eauto. }
    done.
  }
  iDestruct "HTq" as (i s -> HEl) "(#HSegLoc & #HRend & HTq & HInhToken)".
  iSplitR "HInhToken".
  {
    iExists _, _, _. iFrame.
    replace (count_matching _ (drop deqFront' (alter _ _ _))) with
      (count_matching still_present (drop deqFront' l')).
    2: {
      destruct (decide (i < deqFront')%nat).
      by rewrite drop_alter //.
      repeat rewrite count_matching_drop.
      rewrite take_alter; try lia.
      erewrite count_matching_alter; eauto.
      simpl.
      lia.
    }
    by iFrame.
  }

  iIntros "!> HΦ". wp_pures. wp_lam. wp_pures. wp_lam. wp_pures.
  wp_apply (interruptibly_spec _ (inhabitant_token γtq i)
                               (fun _ => thread_has_permit γth ∗ R)%I
                               (fun _ => interrupted γi)
              with "[HInhToken]").
  {
    iFrame "HIntHandle HInhToken".
    iSplit.
    {
      iIntros (Φ') "!> HInhTok HΦ'". wp_pures. wp_bind (!_)%E.
      rewrite /is_thread_handle.
      iInv "HThreadHandle" as (? t) "[>% [Hℓ HThAuth]]" "HClose". simplify_eq.
      wp_load.
      iInv "HSemInv" as (? l'' ?) "(HPerms & >HAuth & HTq & HRest)" "HClose'".
      iAssert (▷ ⌜∃ c, l'' !! i ≡ Some (Some (cellInhabited γth _ c))⌝)%I
        as "#>HI".
      {
        iDestruct "HTq" as "(_ & (_ & _ & >HH' & _) & _)".
        iDestruct "HRend" as "[_ HRend]".
        iApply (cell_list_contents_ra_locs with "HH' HRend").
      }
      iDestruct "HI" as %(r & HEl').
      simplify_eq.
      iAssert (▷ ⌜r = None ∨ r = Some cellResumed⌝)%I as "#>HPures".
      {
        iDestruct "HTq" as "(_ & (_ & _ & _ & _ & _ & HH') & _)".
        iDestruct (big_sepL_lookup with "HH'") as "HRes"; first done.
        simpl. iDestruct "HRes" as (?) "[_ HRes]".
        destruct r as [r|]; last by eauto.
        iRight. iDestruct "HRes" as "(_ & _ & HRes)".
        destruct r.
        2: by eauto.
        1: iDestruct "HRes" as "[>HInhTok' _]".
        2: iDestruct "HRes" as "(_ & >HInhTok' & _)".
        all: by iDestruct (inhabitant_token_exclusive with "HInhTok HInhTok'") as %[].
      }
      iDestruct "HPures" as %HPures.
      iDestruct "HTq" as "(HHead & HListContents & HTail)".
      iDestruct (cell_list_contents_lookup_acc with "HListContents")
        as "[HRes HLcRestore]".
      by erewrite HEl'.
      destruct HPures as [HPures|HPures]; subst; simpl.
      {
        iDestruct "HRes" as (?) "(HArrMapsto & (Hℓ' & >HNoPerms & HRend') & HRest')".
        iAssert (⌜t ≡ true⌝)%I as %HH.
        {
          iDestruct (own_valid_2 with "HThAuth HNoPerms")
            as %[[HH%Some_included _]%prod_included _]%auth_both_valid.
          iPureIntro.
          destruct HH as [[? HOk]|HOk].
          - simpl in *. by apply to_agree_inj.
          - apply prod_included in HOk; simpl in *.
            destruct HOk as [_ HOk].
            by apply to_agree_included in HOk.
        }
        simplify_eq.
        iMod ("HClose'" with "[-Hℓ HThAuth HClose HInhTok HΦ']") as "_".
        {
          iExists _, _, _.
          iDestruct ("HLcRestore" with "[HArrMapsto Hℓ' HNoPerms HRend' HRest']") as "$".
          2: by iFrame.
          iExists _. iFrame.
        }
        iMod ("HClose" with "[Hℓ HThAuth]") as "_".
        {
          iExists _, _. by iFrame.
        }
        iIntros "!>". wp_pures. iApply "HΦ'". iLeft. by iFrame.
      }

      iDestruct "HRes" as (ℓ') "(HArrMapsto & HRendHandle & HIsSus & HIsRes &
        HCancHandle & [[>HInhTok' _]|(Hℓ' & HR & [[>HHasPerm HResTok]|>HNoPerms])])".
      by iDestruct (inhabitant_token_exclusive with "HInhTok HInhTok'") as %[].
      {
        iAssert (⌜t ≡ false⌝)%I as %HH.
        {
          iDestruct (own_valid_2 with "HThAuth HHasPerm")
            as %[[HH%Some_included _]%prod_included _]%auth_both_valid.
          iPureIntro.
          destruct HH as [[? HOk]|HOk].
          - simpl in *. by apply to_agree_inj.
          - apply prod_included in HOk; simpl in *.
            destruct HOk as [_ HOk].
            by apply to_agree_included in HOk.
        }
        simplify_eq.
        iMod ("HClose'" with "[-Hℓ Hℓ' HThAuth HClose HHasPerm HΦ' HR]") as "_".
        {
          iExists _, _, _.
          iDestruct ("HLcRestore" with "[HArrMapsto HRendHandle HIsSus HIsRes
            HCancHandle HInhTok HResTok]") as "$".
          2: by iFrame.
          iExists _. iFrame. iLeft. iFrame "HInhTok". iRight. iFrame "HResTok".
        }
        iMod ("HClose" with "[Hℓ HThAuth]") as "_".
        {
          iExists _, _. by iFrame.
        }
        iIntros "!>". wp_pures. iApply "HΦ'". iRight. iExists _. by iFrame.
      }
      {
        iAssert (⌜t ≡ true⌝)%I as %HH.
        {
          iDestruct (own_valid_2 with "HThAuth HNoPerms")
            as %[[HH%Some_included _]%prod_included _]%auth_both_valid.
          iPureIntro.
          destruct HH as [[? HOk]|HOk].
          - simpl in *. by apply to_agree_inj.
          - apply prod_included in HOk; simpl in *.
            destruct HOk as [_ HOk].
            by apply to_agree_included in HOk.
        }
        simplify_eq.
        iMod ("HClose'" with "[-Hℓ HThAuth HClose HInhTok HΦ']") as "_".
        {
          iExists _, _, _.
          iDestruct ("HLcRestore" with "[HArrMapsto HRendHandle HIsSus HIsRes
            HCancHandle HR Hℓ' HNoPerms]") as "$".
          2: by iFrame.
          iExists _. iFrame. iRight. iFrame "HR Hℓ'".
        }
        iMod ("HClose" with "[Hℓ HThAuth]") as "_".
        {
          iExists _, _. by iFrame.
        }
        iIntros "!>". wp_pures. iApply "HΦ'". iLeft. by iFrame.
      }
    }
    {
      iIntros (Φ') "!> [HInhTok #HInterrupted] HΦ'". wp_pures. wp_bind (FAA _ _).
      iClear "HElExists". clear.
      iInv "HSemInv" as (availablePermits l deqFront)
                          "(HPerms & >HAuth & HTq & Hp & >HPure)" "HInvClose".

      remember (availablePermits - _) as oldP.
      destruct (decide (0 <= oldP)).
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
        iAssert (⌜count_matching still_present (drop deqFront l) = 0%nat⌝)%I
          as %HH.
        by iDestruct "HPure" as %[HH|HH]; subst; iPureIntro; lia.
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
            as "[HH HR]".
          iDestruct "HH" as (? ?) "[(HEl' & HListContents & HRendAbandon)|
                                    (HContra & _)]".
          2: {
            iDestruct "HContra" as %HContra.
            simplify_eq.
          }
          iMod ("HInvClose" with "[-HΦ' HRendAbandon]") as "_".
          {
            iExists _, _, _. iFrame "HAuth". rewrite Nat.add_1_r /=.
            iFrame "HR".
            iSplitL "HPerms".
            {
              iApply (big_opL_forall' with "HPerms").
              by repeat rewrite seq_length.
              done.
            }
            iFrame  "HInfArr HListContents".
            rewrite alter_length.
            iDestruct "HRest" as "[HRest $]".
            iSplitL "HRest".
            {
              destruct (decide (i = deqFront - 1)%nat).
              - subst. rewrite list_lookup_alter. iPureIntro.
                rewrite HEl. simpl. intros [_ (? & ? & HContra)].
                simplify_eq.
              - by rewrite list_lookup_alter_ne.
            }
            rewrite drop_alter; last lia. subst.
            rewrite HH.
            repeat rewrite Z.sub_0_r.
            rewrite Z.add_1_r Nat2Z.inj_succ.
            iFrame "Hp". by iPureIntro; right.
          }
          iModIntro. wp_pures. rewrite bool_decide_decide decide_True //.
          wp_pures.
          iApply "HΦ'".
          iApply "HInterrupted".
        }
        {
          iMod ("HInvClose" with "[-HΦ']") as "_".
          {
            iExists _, _, _.
            iDestruct (cell_list_contents_lookup_acc with "[$]")
                      as "[HRR HListRestore]"; first done.
            simpl. iFrame "HInfArr HRest HAuth". subst.
            rewrite HH. repeat rewrite Z.sub_0_r.
            rewrite Z.add_1_r Nat.add_1_r /= Nat2Z.inj_succ. iFrame "Hp".
            iDestruct "HRR" as (ℓ) "(HArrMapsto & HRendTh & HIsSus & HIsRes &
              HCancHandle & [[HInhTok' _]|(Hℓ & HR & [[HHasPerm HResTok]|HNoPerms])])".
            by iDestruct (inhabitant_token_exclusive with "HInhTok HInhTok'") as %[].
            {
              iDestruct ("HListRestore" with "[HArrMapsto HRendTh HIsSus HIsRes
                HCancHandle HResTok HInhTok]") as "$".
              {
                iExists _. iFrame. iLeft. iFrame.
              }
              iFrame "HR". iSplitL "HPerms".
              { iApply (big_opL_forall' with "HPerms"); last done.
                by repeat rewrite seq_length. }
              iFrame. iPureIntro. right. done.
            }
            {
              iDestruct ("HListRestore" with "[HArrMapsto HRendTh HIsSus HIsRes
                HCancHandle HInhTok HNoPerms]") as "$".
              {
                iExists _. iFrame.
              }
              iFrame "HR". iSplitL "HPerms".
              { iApply (big_opL_forall' with "HPerms"); last done.
                by repeat rewrite seq_length. }
              iFrame. iPureIntro. right. done.
            }
          }
          iModIntro. wp_pures. rewrite bool_decide_decide decide_True //.
          wp_pures.
          iApply "HΦ'". iApply "HInterrupted".
        }
      }
      rewrite /cell_ref_loc.

      remember (count_matching _ _) as v.
      assert (v > 0) as HExistsNondequed by lia.
      move: HExistsNondequed. subst. move=> HExistsNondequed.
      apply count_matching_find_index_Some in HExistsNondequed.
      destruct HExistsNondequed as [? HFindIndex].

      iMod (do_cancel_rendezvous_spec with "HInhTok HTq") as (? ?) "HTT";
        first done.

      admit.
    }
  }
  iIntros (? ?) "[(-> & #HInterrupted)|(-> & HHasPerm & HR)]".
  1: by wp_pures; iApply "HΦ"; eauto.
  wp_pures.
  iAssert (▷ thread_has_permit γth)%I with "[$]" as "HHasPerm".
  awp_apply (thread_update_state with "HThreadHandle") without "HΦ HR".
  iAaccIntro with "HHasPerm".
  by iIntros "$ //".
  iIntros "HNoPerms !> [HΦ HR]".

  wp_pures. iApply "HΦ". iLeft. iFrame. done.
Abort.

End proof.
