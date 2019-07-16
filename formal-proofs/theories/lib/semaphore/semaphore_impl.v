From iris.heap_lang Require Import proofmode.
From iris.heap_lang Require Import notation lang.
Require Import SegmentQueue.lib.thread_queue.thread_queue_spec.

(* The semaphore module definition *)
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
