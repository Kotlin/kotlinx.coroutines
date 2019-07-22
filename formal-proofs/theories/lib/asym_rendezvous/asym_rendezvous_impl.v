From iris.heap_lang Require Import proofmode notation lang.
Require Import SegmentQueue.lib.util.getAndSet.
Require Import SegmentQueue.lib.util.interruptibly.
Require Import SegmentQueue.lib.asym_rendezvous.asym_rendezvous_spec.

Definition new_exchange : val :=
  λ: <>, ref NONE.

Definition init_exchange : val :=
  λ: "ℓ", "ℓ" <- NONE.

Definition await : val :=
  rec: "await" "e" := (match: !"e" with
                         NONE => "await" "e"
                       | SOME "v" => if: "v" = #1 then !#0 else #()
                       end)%E.

Definition await_interruptibly : val :=
  (loop:
    (λ: "e", !"e")%V
  interrupted:
    (λ: "e", getAndSet "e" CANCELLED)%V)%E.

Definition pass : val := λ: "e", getAndSet "e" RESUMEDV.
