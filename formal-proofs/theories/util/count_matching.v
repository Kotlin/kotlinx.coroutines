From Coq Require Import ssreflect.
Require Import stdpp.base stdpp.list.
Require Import SegmentQueue.util.find_index.

Fixpoint count_matching {A} (P: A -> Prop) {H': forall x, Decision (P x)} (l: list A): nat :=
  match l with
  | nil => 0
  | cons x l' => if decide (P x) then S (count_matching P l') else count_matching P l'
  end%GEN_IF.

Theorem count_matching_is_length_filter {A} (P: A -> Prop) {H': forall x, Decision (P x)} l:
  count_matching P l = length (filter P l).
Proof.
  induction l; auto.
  simpl. unfold filter in *. simpl.
  destruct (decide (P a)); simpl; auto.
Qed.

Theorem count_matching_app {A} (P: A -> Prop) {H': forall x, Decision (P x)} (l1 l2: list A):
  count_matching P (l1 ++ l2) = (count_matching P l1 + count_matching P l2)%nat.
Proof. repeat rewrite count_matching_is_length_filter.
         by rewrite filter_app app_length. Qed.

Theorem count_matching_alter
        {A} (P: A -> Prop) {H': forall x, Decision (P x)}:
  let to_num x := (if decide (P x) then 1%nat else 0%nat)%GEN_IF in
  forall v f l i, l !! i = Some v ->
               count_matching P (alter f i l) =
               (count_matching P l + (to_num (f v)) - (to_num v))%nat.
Proof.
  induction l; rewrite /= //; unfold to_num in *.
  case; rewrite /=.
  { intros. simplify_eq. destruct (decide (P v)); destruct (decide (P (f v))).
    all: rewrite /=; lia. }
  intros n Hel. rewrite /filter /=. destruct (decide (P a)); rewrite /= IHl //.
  destruct (decide (P v)) as [pv|]; simpl. 2: lia.
  destruct (count_matching P l) eqn:Z.
  2: destruct (decide (P (f v))); simpl; lia.
  exfalso.
  move: n Z Hel pv. clear. induction l.
  - intros. inversion Hel.
  - intros. destruct n.
    * inversion Hel. subst. simpl in *. destruct (decide (P v)); done.
    * inversion Hel. eapply IHl; try done. simpl in *.
      by destruct (decide (P a)).
Qed.

Theorem count_matching_le_length
        {A} (P: A -> Prop) {H': forall x, Decision (P x)} (l: list A):
  (count_matching P l <= length l)%nat.
Proof. induction l; first done. simpl. destruct (decide (P a)); lia. Qed.

Theorem count_matching_complement
        {A} (P: A -> Prop) {H': forall x, Decision (P x)} (l: list A):
  count_matching (fun b => not (P b)) l = (length l - count_matching P l)%nat.
Proof.
  induction l; first done.
  simpl.
  destruct (decide (P a)); destruct (decide (not (P a))); try contradiction.
  done.
  rewrite -minus_Sn_m.
  by apply count_matching_le_length.
  lia.
Qed.

Theorem count_matching_take
        {A} (P: A -> Prop) {H': forall x, Decision (P x)} (l: list A):
  forall i, count_matching P (take i l) =
       (count_matching P l - count_matching P (drop i l))%nat.
Proof.
  intros i.
  replace (count_matching P l) with (count_matching P (take i l ++ drop i l)).
  2: by rewrite take_drop.
  rewrite count_matching_app. lia.
Qed.

Theorem count_matching_drop
        {A} (P: A -> Prop) {H': forall x, Decision (P x)} (l: list A):
  forall i, count_matching P (drop i l) =
       (count_matching P l - count_matching P (take i l))%nat.
Proof.
  intros i.
  replace (count_matching P l) with (count_matching P (take i l ++ drop i l)).
  2: by rewrite take_drop.
  rewrite count_matching_app. lia.
Qed.

Lemma present_cells_in_take_i_if_next_present_is_Si
  {A: Type} (P: A -> Prop) {H': forall x, Decision (P x)} (i: nat) (l: list A):
    find_index P l = Some i ->
    count_matching P (take i l) = O.
Proof.
  intros HFindSome.
  apply find_index_Some in HFindSome.
  destruct HFindSome as [[v [HIn HPresent]] HNotPresent].
  assert (i < length l)%nat as HLt.
  { apply lookup_lt_is_Some. by eexists. }

  assert (forall i', (i' < i)%nat -> exists v', take i l !! i' = Some v' /\
                                      not (P v')) as HH.
  {
    intros i' HLti'. destruct (HNotPresent i' HLti')
      as [v' [HEl Hv'NotPresent]].
    exists v'. split; try done. by rewrite lookup_take.
  }
  remember (take i l) as l'. assert (i = length l') as HLen.
  by subst; rewrite take_length_le; lia.
  subst i.
  revert HH. clear. rewrite /count_matching /filter /=.
  induction l'; auto=> H. simpl in *.
  destruct (H O) as [p H'']; simpl in *; first by lia.
  destruct H'' as [[=] HH]; subst. destruct (decide (P p)).

  contradiction.
  apply IHl'.
  intros i' HLt.
  destruct (H (S i')); first by lia.
  simpl in *. eauto.
Qed.

Lemma present_cells_in_take_1_drop_i_if_next_present_is_Si
  {A: Type} (P: A -> Prop) {H': forall x, Decision (P x)} (i: nat) (l: list A):
    find_index P l = Some i ->
    count_matching P (take 1 (drop i l)) = 1%nat.
Proof.
  intros HFindSome.
  apply find_index_Some in HFindSome.
  destruct HFindSome as [[v [HIn HPresent]] HNotPresent].
  assert (i < length l)%nat as HLt.
  { apply lookup_lt_is_Some. by eexists. }

  replace (drop i l) with (v :: drop (S i) l).
  { simpl. destruct (decide (P v)); try contradiction. done. }
  assert (i = length (take i l))%nat as HH.
  by rewrite take_length_le; lia.
  replace (drop i l) with (drop i (take i l ++ v :: drop (S i) l)).
  { symmetry. rewrite drop_app_le. lia. rewrite drop_ge. lia. done. }
  by rewrite take_drop_middle.
Qed.

Lemma present_cells_in_take_Si_if_next_present_is_Si
  {A: Type} (P: A -> Prop) {H': forall x, Decision (P x)} (i: nat) (l: list A):
    find_index P l = Some i ->
    count_matching P (take (S i) l) = 1%nat.
Proof.
  intros HFindSome.
  change (S i) with (1 + i)%nat.
  rewrite Nat.add_comm -take_take_drop count_matching_app.
  rewrite present_cells_in_take_1_drop_i_if_next_present_is_Si //.
  rewrite present_cells_in_take_i_if_next_present_is_Si //.
Qed.

Lemma absent_cells_in_drop_Si_if_next_present_is_i
  {A: Type} (P: A -> Prop) {H': forall x, Decision (P x)} (i: nat) (l: list A):
    find_index P l = Some i ->
  count_matching (λ b, not (P b)) l =
  (i + count_matching (λ b, not (P b)) (drop (S i) l))%nat.
Proof.
  intros HFindSome.
  repeat rewrite count_matching_complement.
  rewrite drop_length.

  replace (count_matching P l) with
      (count_matching P (take (S i) l ++ drop (S i) l)).
  2: by rewrite take_drop.

  rewrite count_matching_app Nat.sub_add_distr.
  rewrite present_cells_in_take_Si_if_next_present_is_Si; try done.

  repeat rewrite -Nat.sub_add_distr /=.
  remember (count_matching (_) (drop (S i) _)) as K.
  rewrite plus_n_Sm.
  rewrite -(Nat.add_comm (S K)) Nat.sub_add_distr.
  assert (K <= length l - S i)%nat as HKLt.
  {
    rewrite HeqK. eapply transitivity.
    apply count_matching_le_length.
    by rewrite drop_length.
  }
  assert (i < length l)%nat; try lia.
  apply find_index_Some in HFindSome.
  destruct HFindSome as [(v & HEl & _) _].
  apply lookup_lt_is_Some. eauto.
Qed.

Theorem count_matching_find_index_Some A (P: A -> Prop) (H': forall x, Decision (P x)) l:
  (count_matching P l > 0)%nat -> is_Some (find_index P l).
Proof.
  induction l; simpl; first lia.
  destruct (decide (P a)); first by eauto.
  destruct (find_index P l); by eauto.
Qed.
