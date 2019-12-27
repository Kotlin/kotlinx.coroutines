From iris.heap_lang Require Import notation.

Require Import SegmentQueue.lib.thread_queue.thread_queue.

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
     then #false
     else
       if: CAS "ctr" "arrived" ("arrived" + #1)
       then if: "canceller" #()
            then #()
            else resume segment_size "head" "deqIdx"
              ;;
            #true
       else "loop" "ctr" "head" "deqIdx" "canceller".

Definition await : val :=
  λ: "threadHandle" "ctr" "tail" "enqIdx" "head" "deqIdx",
  let: "p" := FAA "ctr" #1
  in if: "p" = #(Pos.to_nat limit-1)
     then forRange "p" (λ: "i", resume segment_size "head" "deqIdx")
     else suspend segment_size (cancellation_handler "ctr" "head" "deqIdx")
                  "cancHandle" "threadHandle" "tail" "enqIdx".

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

Context `{!heapG Σ}.

Theorem forRange_spec (Φ: nat -> iProp Σ) (e: val):
  (∀ i, {{{ Φ i }}}
           e #i
         {{{ v, RET v; Φ (S i) }}})
   -∗
   (∀ n, {{{ Φ O }}}
           forRange #n e
         {{{ v, RET v; Φ n }}}).
Proof.
  iIntros "#HE" (n Ψ).
  iInduction n as [|n'] "IH" forall (Ψ); iIntros "!> HΦ0 HΨ"; wp_lam; wp_pures.
  by iApply "HΨ".
  replace #(S n' - 1) with #n'; last by congr (fun x => LitV (LitInt x)); lia.
  wp_bind (forRange _ _).
  wp_apply ("IH" with "HΦ0").
  iIntros (v) "HΦn".
  wp_pures.
  replace #(S n' - 1) with #n'; last by congr (fun x => LitV (LitInt x)); lia.
  by wp_apply ("HE" with "HΦn").
Qed.

End proof.

Section barrier_proof.

Variable (limit: positive).

Notation algebra := (authR (optionUR (csumR positiveR positiveR))).

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

Definition barrier_entry_piece γ := own γ (◯ (Some (Cinl 1%positive))).
Definition barrier_exit_piece γ := own γ (◯ (Some (Cinr 1%positive))).

Definition is_barrier_inv γ (ℓ: loc) (n: nat)
  (epℓ eℓ dpℓ dℓ: loc) (γa γtq γe γd: gname) :=
  (∃ l deqFront, own γ (● (Some (Cinl limit))) ∗
    ℓ ↦ #n ∗ (if decide (n < Pos.to_nat limit)%nat
              then [∗] replicate n (barrier_entry_piece γ)
              else True) ∗
    is_thread_queue (N .@ "tq") Nth segment_size True (barrier_exit_piece γ)
    γa γtq γe γd eℓ epℓ dℓ dpℓ l deqFront ∗
    let v := count_matching still_present (drop deqFront l) in
    (⌜if decide (n < Pos.to_nat limit)%nat then v = n else v = O⌝))%I.



End barrier_proof.
