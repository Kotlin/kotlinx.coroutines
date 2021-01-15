From iris.proofmode Require Import tactics.
From iris.program_logic Require Export atomic.
From iris.heap_lang Require Import proofmode notation lang.
From SegmentQueue.util Require Import everything.

Definition forRange : val :=
  rec: "loop" "n" "fn" :=
    if: "n" ≤ #0
    then #()
    else "loop" ("n"-#1) "fn" ;; "fn" ("n"-#1).

Section for_proof.

Context `{!heapG Σ}.

Theorem forRange_spec (Φ: nat -> iProp Σ) (e: val) (n: nat):
  (∀ i, ⌜(i < n)%nat⌝ -∗ {{{ Φ i }}}
                           e #i
                         {{{ v, RET v; Φ (S i) }}})
   -∗
   {{{ Φ O }}}
     forRange #n e
   {{{ v, RET v; Φ n }}}.
Proof.
  iIntros "#HE" (Ψ).
  iInduction n as [|n'] "IH" forall (Ψ); iIntros "!> HΦ0 HΨ"; wp_lam; wp_pures.
  by iApply "HΨ".
  replace #(S n' - 1) with #n'; last by congr (fun x => LitV (LitInt x)); lia.
  wp_bind (forRange _ _).
  wp_apply ("IH" with "[] HΦ0").
  { iIntros "!>" (i HLt). iApply "HE". iPureIntro. lia. }
  iIntros (v) "HΦn".
  wp_pures.
  replace #(S n' - 1) with #n'; last by congr (fun x => LitV (LitInt x)); lia.
  wp_apply ("HE" with "[] HΦn"); last done.
  iPureIntro. lia.
Qed.

Theorem forRange_resource_map (Φ Ψ: nat -> iProp Σ) (e: val):
  (∀ (i: nat), {{{ Φ i }}}
                 e #i
                 {{{ v, RET v; Ψ i }}})
    -∗
  (∀ n, {{{ [∗ list] i ∈ seq 0 n, Φ i }}}
          forRange #n e
        {{{ v, RET v; [∗ list] i ∈ seq 0 n, Ψ i }}}).
Proof.
  iIntros "#HE" (n Ξ) "!> HΦ HΨ".
  iApply (forRange_spec
            (fun j => ([∗ list] i ∈ seq j (n-j), Φ i) ∗
                   ([∗ list] i ∈ seq 0 j, Ψ i))%I
            with "[] [HΦ]").
  - iIntros (i HLt). iIntros "!>" (?) "HPre HPost".
    replace (seq 0 (S i)) with (seq 0 (i + 1)) by (congr (seq 0); lia).
    rewrite seq_add /=.
    destruct (n - i)%nat as [|ni] eqn:X; first by lia.
    simpl.
    iDestruct "HPre" as "[[HΦi HΦ] HΨ]".
    wp_apply ("HE" with "HΦi").
    iIntros (v) "HΨi".
    iApply "HPost".
    replace (n - S i)%nat with ni by lia. iFrame. done.
  - rewrite Nat.sub_0_r. simpl. iFrame.
  - iIntros (v) "!> HH".
    iApply "HΨ".
    iDestruct "HH" as "[_ $]".
Qed.

End for_proof.
