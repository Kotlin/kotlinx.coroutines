From iris.base_logic.lib Require Export invariants.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation lang.
From iris.program_logic Require Export weakestpre atomic.
From iris.algebra Require Import cmra.
Require Import thread_queue_spec.
Set Default Proof Using "Type".

(*
From iris.heap_lang Require Import notation lang proofmode.

Record threadQueue {Σ} `{heapG Σ} := ThreadQueue {
  (* -- operations -- *)
  new_thread_queue: val;
  add_to_queue_and_suspend: val;
  resume_next_from_queue: val;
  (* -- predicates -- *)
  thread_queue_name: Type;
  is_thread_queue
    (N: namespace)
    (γ: thread_queue_name)
    (queue: val)
    (Q: iProp Σ) : iProp Σ;
  (* -- general properties -- *)
  is_thread_queue_persistent N γ queue Q : Persistent (is_thread_queue N γ queue Q);
  is_thread_queue_ne N γ queue : NonExpansive (is_thread_queue N γ queue);
  (* -- operation specs -- *)
  new_thread_queue_spec N Q:
    {{{ True }}} new_thread_queue #() {{{ l γ, RET l; is_thread_queue N γ l Q }}};
  add_to_queue_and_suspend_spec N γ l Q:
    {{{ is_thread_queue N γ l Q }}}
      add_to_queue_and_suspend l
    {{{ RET #(); Q }}};
  resume_next_from_queue_spec N γ l Q:
    {{{ is_thread_queue N γ l Q ∗ Q }}}
      resume_next_from_queue l
    {{{ RET #(); True }}}
}.

Existing Instances is_thread_queue_persistent.
Existing Instances is_thread_queue_ne.
 *)

Section exchange.

  Definition new_exchange : val :=
    λ: <>, ref NONE.

  Definition await_on (f : expr) r :=
    (match: !"e" with
       NONE => f "e"
     | SOME "v" => r "v"
     end)%E.

  Definition await : val :=
    rec: "await" "e" := await_on "await"%E id.

  Definition await_interruptibly : val :=
    rec: "await" "h" "e" :=
      if: !"h" = #0
      then await_on ("await_int" "h") (fun x => SOME x)
      else NONE.

  Definition pass : val := λ: "e" "v", "e" <- SOME "v".

End exchange.

(*
Section thread_queue.

  Definition new_thread_queue_sq : val :=
    λ: "id", ref (ref #0, ref #0, new_infinite_array new_exchange)%E.

  Definition add_to_queue_and_suspend_sq : val :=
    λ: "q", let: "enqIdx" := Fst (Fst (!"q")) in
            let: "array" := Snd (!"q") in
            let: "tail" := infinite_array_tail "array" in
            let: "i" := FAA "enqIdx" 1 in
            let: "ex" := infinite_array_get "array" "tail" "i" in
            await "ex".

  Definition resume_next_from_queue_sq : val :=
    λ: "q", let: "deqIdx" := Snd (Fst (!"q")) in
            let: "array" := Snd (!"q") in
            let: "head" := infinite_array_head "array" in
            let: "i" := FAA "deqIdx" 1 in
            let: "ex" := infinite_array_get_pop "array" "head" "i" in
            pass "ex" #().

End thread_queue.

Section semaphore.

  Context `{heapG Σ} (N : namespace).
  Notation iProp := (iProp Σ).
  Variable q : threadQueue.

  Definition new_semaphore_sq : val := λ: "k",
                                       ref (ref "k", new_thread_queue q #())%E.
  Definition acquire_sq : val := λ: "s", let: "p" := FAA (Fst !"s") #(-1) in
                                         let: "q" := Snd !"s" in
                                         if: #0 < "p"
                                           then #()
                                           else add_to_queue_and_suspend q "q".
  Definition release_sq : val := λ: "s", let: "p" := FAA (Fst !"s") #1 in
                                         let: "q" := Snd !"s" in
                                         if: #0 ≤ "p"
                                           then #()
                                           else resume_next_from_queue q "q".
End semaphore.

Section proof.

  Class mSemaphoreG Σ := MSemaphoreG { msemaphore_inG :> inG Σ boundedPosR }.
  Definition mSemaphoreΣ : gFunctors := #[GFunctor boundedPosR].
  Instance subG_msemaphoreΣ {Σ} : subG mSemaphoreΣ Σ -> mSemaphoreG Σ.
  Proof. solve_inG. Qed.

  Context `{mSemaphoreG Σ}.
  Context `{heapG Σ}.
  Notation iProp := (iProp Σ).

  Variable tq : threadQueue.
  Variable (N: namespace).

  Definition permit_sq (γ: gname) (perms : nat) :=
    own γ (bpos 1 (Pos.of_nat (1 + perms))).

  Definition semaphore_inv γ (z : val) (ℓ pℓ : loc) (perms : nat) (R : iProp) : iProp :=
    (∃ (p : Z), ℓ ↦ z ∗ pℓ ↦ #p ∗
                ((∃ n, ⌜p = (1 + Z.of_nat n)%Z⌝ ∧
                       iPropPow (S n) R ∗ iPropPow (S n) (own γ (bpos 1 (Pos.of_nat (S perms))))) ∨
                 ⌜(p <= 0)%Z⌝))%I.

  Definition is_semaphore_sq
             (N : namespace)
             (γ: gname)
             (semaphore: val)
             (perms: nat)
             (R: iProp) :=
    (∃ (ℓ pℓ: loc) (q : val), ⌜semaphore = #ℓ⌝ ∧
                           (∃ γ', is_thread_queue tq N γ' q (permit_sq γ perms ∗ R)) ∧
                           inv N (semaphore_inv γ (#pℓ, q) ℓ pℓ perms R))%I.

  Global Instance is_semaphore_persistent_sq γ sem p R:
    Persistent (is_semaphore_sq N γ sem p R).
  Proof. apply _. Qed.

  Global Instance permit_timeless_sq γ p : Timeless (permit_sq γ p).
  Proof. apply _. Qed.

  Global Instance iPropPow_ne Σ n: NonExpansive (@iPropPow Σ n).
  Proof. induction n; solve_proper. Qed.

  Global Instance semaphore_inv_ne γ z ℓ pℓ perms: NonExpansive (semaphore_inv γ z ℓ pℓ perms).
  Proof. solve_proper. Qed.

  Global Instance is_semaphore_ne_sq N γ sem p: NonExpansive (is_semaphore_sq N γ sem p).
  Proof. solve_proper. Qed.
*)
