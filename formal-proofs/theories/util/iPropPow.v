Require Import iris.bi.interface.
Require Import iris.base_logic.lib.iprop.

Fixpoint iPropPow {Σ} (n : nat) (p : iProp Σ) : iProp Σ :=
  match n with
  | O => (True)%I
  | S n => (p ∗ iPropPow n p)%I
  end.
