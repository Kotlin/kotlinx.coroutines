Require Import SegmentQueue.util.everything.
From Coq Require Import ssreflect.
Require Import stdpp.base stdpp.list.
Require Import SegmentQueue.util.find_index.

Fixpoint count_matching {A} (P: A -> Prop) {H': forall x, Decision (P x)} (l: list A): nat :=
  match l with
  | nil => 0
  | cons x l' => if decide (P x) then S (count_matching P l') else count_matching P l'
  end%GEN_IF.

Definition sum := foldr Nat.add 0.

Theorem sum_app a b: sum (a ++ b) = sum a + sum b.
Proof. induction a=> //=. rewrite IHa; lia. Qed.

Theorem count_matching_is_sum_map {A} (P: A -> Prop) {H': forall x, Decision (P x)} l:
  count_matching P l =
  sum (map (fun x => if decide (P x) then 1 else 0)%GEN_IF l).
Proof. induction l; auto. simpl. destruct (decide (P a)); simpl; auto. Qed.

Theorem count_matching_app {A} (P: A -> Prop) {H': forall x, Decision (P x)} (l1 l2: list A):
  count_matching P (l1 ++ l2) = (count_matching P l1 + count_matching P l2)%nat.
Proof. rewrite !count_matching_is_sum_map map_app sum_app //. Qed.

Theorem count_matching_alter
        {A} (P: A -> Prop) {H': forall x, Decision (P x)}:
  let to_num x := (if decide (P x) then 1%nat else 0%nat)%GEN_IF in
  forall v f l i, l !! i = Some v ->
               count_matching P (alter f i l) =
               (count_matching P l + (to_num (f v)) - (to_num v))%nat.
Proof.
  intros ? v f l i HEl. rewrite -[in count_matching P l](take_drop_middle l i v HEl).
  erewrite take_drop_middle_alter; last done.
  rewrite !count_matching_is_sum_map.
  rewrite !map_app !sum_app=> /=. subst to_num. simpl. lia.
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
  rewrite -minus_Sn_m; try lia.
  by apply count_matching_le_length.
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

Theorem count_matching_all
  {A} (P: A -> Prop) {H': forall x, Decision (P x)} (l: list A):
  count_matching P l = length l <-> ∀ i, i ∈ l → P i.
Proof.
  split.
  - induction l as [|a l]=> /=.
    * intros _ i Hi. inversion Hi.
    * destruct (decide (P a)).
      + case. intros HOk i Hi.
        inversion Hi; subst; first done. by apply IHl.
      + intros HContra.
        assert (count_matching P l ≤ length l); last lia.
        apply count_matching_le_length.
  - intros HEl. induction l as [|a l] => //=.
    rewrite decide_True; last by apply HEl; constructor.
    rewrite IHl //.
    intros i Hi. apply HEl. by constructor.
Qed.

Theorem count_matching_none
  {A} (P: A -> Prop) {H': forall x, Decision (P x)} (l: list A):
  count_matching P l = 0 <-> ∀ i, i ∈ l → ¬ P i.
Proof.
  assert (count_matching P l = 0 <->
          count_matching (fun b => ¬ (P b)) l = length l) as ->.
  {
    rewrite count_matching_complement.
    assert (count_matching P l ≤ length l).
    by apply count_matching_le_length.
    split; lia.
  }
  apply count_matching_all.
Qed.

Lemma present_cells_in_take_i_if_next_present_is_Si
  {A: Type} (P: A -> Prop) {H': forall x, Decision (P x)} (i: nat) (l: list A):
    find_index P l = Some i ->
    count_matching P (take i l) = O.
Proof.
  intros HFindSome. apply count_matching_none.
  apply find_index_Some in HFindSome. intros v HEl.
  destruct HFindSome as [_ HNotPresent].
  apply elem_of_list_lookup_1 in HEl. destruct HEl as [i' HEl].
  destruct (decide (i ≤ i')).
  by rewrite lookup_take_ge in HEl; last lia.
  rewrite lookup_take in HEl; last lia.
  destruct (HNotPresent i') as (v' & HEl' & HProof); first lia.
  by simplify_eq.
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
  { symmetry. rewrite drop_app_le; last lia. rewrite drop_ge //. lia. }
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
