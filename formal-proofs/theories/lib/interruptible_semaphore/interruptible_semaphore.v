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

From iris.heap_lang Require Import proofmode.
From iris.algebra Require Import auth.
From iris.algebra Require Import list gset excl csum.
From iris.program_logic Require Import atomic.

Require Import SegmentQueue.lib.infinite_array.infinite_array_impl.
Require Import SegmentQueue.lib.infinite_array.iterator.

Section proof.

Notation algebra := (authR (prodUR natUR natUR)).

Class semaphoreG Σ := SemaphoreG { semaphore_inG :> inG Σ algebra }.
Definition semaphoreΣ : gFunctors := #[GFunctor algebra].
Instance subG_semaphoreΣ {Σ} : subG semaphoreΣ Σ -> semaphoreG Σ.
Proof. solve_inG. Qed.

Context `{iArrayG Σ} `{iteratorG Σ} `{heapG Σ} `{threadQueueG Σ} `{semaphoreG Σ} `{parkingG Σ}.
Variable (N: namespace).
Notation iProp := (iProp Σ).

Variable (segment_size: positive).

Definition is_semaphore (R : iProp) (γ: gname) (availablePermits: nat) (p: loc)
  (epℓ eℓ dpℓ dℓ: loc) (γa γtq γe γd: gname) :=
  (∃ (readyToCancel: nat) l deqFront,
  ([∗ list] _ ∈ seq 0 availablePermits, R) ∗
   own γ (● (availablePermits, readyToCancel)) ∗
   is_thread_queue N segment_size True R γa γtq γe γd eℓ epℓ dℓ dpℓ l deqFront ∗
   let v := count_matching still_present (drop deqFront l) in
   p ↦ #(availablePermits - v + readyToCancel) ∗
   ⌜readyToCancel <= v ∧ (availablePermits = 0 ∨ v = readyToCancel)%nat⌝)%I.

Theorem release_semaphore_spec R γ (p epℓ eℓ dpℓ dℓ: loc) γa γtq γe γd:
  R -∗
  <<< ∀ availablePermits, is_semaphore R γ availablePermits p epℓ eℓ dpℓ dℓ γa γtq γe γd >>>
    (release_semaphore segment_size) #p #dℓ #dpℓ @ ⊤
  <<< is_semaphore R γ (1 + availablePermits)%nat p epℓ eℓ dpℓ dℓ γa γtq γe γd, RET #() >>>.
Proof.
  iIntros "HR" (Φ) "AU". wp_lam. wp_pures.
  wp_bind (FAA _ _).
  iMod "AU" as (availablePermits) "[HIsSem HClose]".
  iDestruct "HIsSem" as (readyToCancel l deqFront) "(HPerms & HAuth & HTq & Hp & HPure)".
  iDestruct "HPure" as %HPure.
  remember (count_matching _ _) as v.
  remember (availablePermits - v + readyToCancel) as op.
  wp_faa.
  destruct (decide (0 <= op)).
  {
    iDestruct "HClose" as "[_ HClose]".
    iMod (own_update with "HAuth") as "[HAuth HFrag]".
    {
      apply auth_update_alloc.
      apply prod_local_update_1.
      apply (nat_local_update availablePermits 0%nat _ 1%nat).
      auto.
    }
    repeat rewrite Nat.add_1_r.
    iMod ("HClose" with "[-]") as "HΦ".
    {
      iExists _, _, _. simpl. iFrame "HR HAuth HTq".
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
    destruct (decide (0 <= op)); try lia. by wp_pures.
  }

  assert (v > 0) as HExistsNondequed by lia.
  move: HExistsNondequed. subst; clear. move=> HExistsNondequed.

  iDestruct "HTq" as "(HInfArr & HListContents & HRest)".
  iDestruct (cell_list_contents_register_for_dequeue
               with "HR HListContents") as ">[[HAwak HDeqFront] [HListContents _]]".
  {
    admit.
  }

  iDestruct "HClose" as "[HClose _]".
  iMod ("HClose" with "[-HDeqFront HAwak]") as "HΦ".
  {
    iExists _, _, _. iFrame "HAuth HPerms HInfArr".

Abort.

End proof.
