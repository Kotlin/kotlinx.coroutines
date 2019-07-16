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
