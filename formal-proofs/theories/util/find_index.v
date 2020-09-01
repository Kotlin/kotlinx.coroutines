Require Import stdpp.base stdpp.list.

Fixpoint find_index {A} (P: A -> Prop) {H': forall x, Decision (P x)}
         (l: list A): option nat :=
  match l with
  | nil => None
  | cons x l => if decide (P x) then Some 0%nat
               else option_map S (find_index P l)
  end.

From Coq Require Import ssreflect.

Lemma find_index_Some {A} (P: A -> Prop) {H': forall x, Decision (P x)}:
  forall l i, find_index P l = Some i ->
         (exists v, l !! i = Some v /\ P v) /\
         (forall i', (i' < i)%nat -> exists v', l !! i' = Some v' /\ not (P v')).
Proof.
  induction l; first done; simpl in *.
  case; simpl; destruct (decide (P a)).
  by intros _; split; [eauto|intros i; lia].
  by destruct (find_index P l).
  done.
  destruct (find_index P l); try done.
  simpl in *.
  intros n' ?; simplify_eq.
  destruct (IHl _ eq_refl) as [HEl HRst].
  split; first done.
  case; simpl; first by eauto.
  intros. apply HRst. lia.
Qed.

Lemma find_index_None {A} (P: A -> Prop) {H': forall x, Decision (P x)}:
  forall l, find_index P l = None -> forall v, In v l -> not (P v).
Proof.
  induction l; simpl; first done.
  destruct (decide (P a)); first done.
  destruct (find_index P l); first done.
  intros _ ? HEv; subst.
  inversion HEv; subst; eauto.
Qed.
