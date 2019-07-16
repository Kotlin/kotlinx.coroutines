From iris.heap_lang Require Import proofmode.
From iris.heap_lang Require Import notation lang.
Require Import SegmentQueue.lib.thread_queue.thread_queue_spec.
Require Export SegmentQueue.util.iPropPow.

Record semaphore {Σ} `{heapG Σ} := Semaphore {
  (* -- operations -- *)
  new_semaphore: val;
  acquire: val;
  release: val;
  (* -- predicates -- *)
  semaphore_names: Type;
  is_semaphore
    (N: namespace)
    (γ: semaphore_names)
    (semaphore: val)
    (perms: nat)
    (R : iProp Σ) : iProp Σ;
  permit (γ: semaphore_names) (p : nat) : iProp Σ;
  (* -- general properties -- *)
  is_semaphore_persistent N γ sm p R: Persistent (is_semaphore N γ sm p R);
  permit_timeless γ p : Timeless (permit γ p);
  is_semaphore_ne N γ sm p: NonExpansive (is_semaphore N γ sm p);
  permit_k_exclusive γ p:
    iPropPow (1 + p) (permit γ p) -∗ False;
  (* -- operation specs -- *)
  new_semaphore_spec N p R:
    {{{ iPropPow p R }}}
      new_semaphore #p
    {{{ sm γ, RET sm; is_semaphore N γ sm p R}}};
  acquire_spec N γ sm p R:
    {{{ is_semaphore N γ sm p R }}}
      acquire sm
    {{{ RET #(); permit γ p ∗ R }}};
  release_spec N γ sm p R:
    {{{ is_semaphore N γ sm p R ∗ permit γ p ∗ R }}}
      release sm
    {{{ RET #(); True }}}
}.

Existing Instances is_thread_queue_persistent.
Existing Instances is_thread_queue_ne.
