From iris.algebra Require Import cmra auth list agree csum excl gset frac numbers.
From SegmentQueue.util Require Import cmra.

Lemma list_lookup_local_update {A: ucmraT}:
  forall (x y x' y': list A),
    (forall i, (x !! i, y !! i) ~l~> (x' !! i, y' !! i)) ->
    (x, y) ~l~> (x', y').
Proof.
  intros x y x' y' Hup.
  apply local_update_unital=> n z Hxv Hx.
  unfold local_update in Hup.
  simpl in *.
  assert (forall i, ✓{n} (x' !! i) /\ x' !! i ≡{n}≡ (y' ⋅ z) !! i) as Hup'.
  { intros i. destruct (Hup i n (Some (z !! i))); simpl in *.
    - by apply list_lookup_validN.
    - rewrite -list_lookup_op.
      by apply list_dist_lookup.
    - rewrite list_lookup_op. split; done.
  }
  split; [apply list_lookup_validN | apply list_dist_lookup].
  all: intros i; by destruct (Hup' i).
Qed.

Lemma list_append_local_update {A: ucmraT}:
  forall (x z: list A), (forall n, ✓{n} z) -> (x, ε) ~l~> (x ++ z, (replicate (length x) ε) ++ z).
Proof.
  intros ? ? Hzv. apply local_update_unital=> n mz Hxv Hx.
  split; first by apply Forall_app_2; [apply Hxv|apply Hzv].
  rewrite Hx.
  replace (ε ⋅ mz) with mz by auto.
  rewrite list_op_app_le.
  2: by rewrite replicate_length.
  assert (replicate (length mz) ε ⋅ mz ≡ mz) as Heq.
  { clear. apply list_equiv_lookup.
    induction mz; simpl; first done.
    destruct i; simpl.
    by rewrite ucmra_unit_left_id.
    done.
  }
  by rewrite Heq.
Qed.

Lemma list_alter_local_update {A: ucmraT}:
  forall n f g (x y: list A),
    (x !! n, y !! n) ~l~> (f <$> (x !! n), g <$> (y !! n)) ->
    (x, y) ~l~> (alter f n x, alter g n y).
Proof.
  intros ? ? ? ? ? Hup.
  apply list_lookup_local_update.
  intros i.
  destruct (nat_eq_dec i n); subst.
  - by repeat rewrite list_lookup_alter.
  - by repeat rewrite list_lookup_alter_ne.
Qed.

Lemma None_local_update {A: cmraT}: forall (x: A) a b, (None, Some x) ~l~> (a, b).
Proof.
  intros. apply local_update_valid0=> _ _ [HContra|HContra].
  - inversion HContra.
  - apply option_includedN in HContra.
    destruct HContra as [?|(? & ? & ? & ? & _)]; discriminate.
Qed.

Lemma local_update_refl {A: cmraT}: forall (a b: A),
  (a, b) ~l~> (a, b).
Proof. done. Qed.

Lemma option_local_update' {A: ucmraT} (x x' y': A):
  (x, ε) ~l~> (x', y') -> (Some x, ε) ~l~> (Some x', Some y').
Proof.
  intros HOld. apply local_update_unital. intros ? ?.
  rewrite ucmra_unit_left_id => HValid HEq. rewrite -HEq.
  destruct (HOld n (Some x)); rewrite /= //.
  by rewrite ucmra_unit_left_id.
  simpl in *. split; try done. rewrite -Some_op. by constructor.
Qed.

Lemma option_local_update'' {A: cmraT} (x y: A):
  (forall n, ✓{n} x -> ✓{n} (y ⋅ x)) ->
  (Some x, ε) ~l~> (Some (y ⋅ x), Some y).
Proof.
  intros HValidYX. apply local_update_unital.
  intros ? ? HValid'. rewrite ucmra_unit_left_id.
  intros <-. rewrite -Some_op. split; try done.
  apply Some_validN. auto.
Qed.

Lemma option_local_update''' {A: cmraT} (x y z: A):
  z ≡ y ⋅ x ->
  (forall n, ✓{n} x -> ✓{n} (y ⋅ x)) ->
  (Some x, ε) ~l~> (Some z, Some y).
Proof. intros ->. apply option_local_update''. Qed.

Lemma list_lookup_local_update' {A: ucmraT}:
  forall (x y x' y': list A),
    (forall i, (x !! i, y !! i) ~l~> (x' !! i, y' !! i)) ->
    (x, y) ~l~> (x', y').
Proof.
  intros x y x' y' Hup.
  apply local_update_unital=> n z Hxv Hx.
  unfold local_update in Hup.
  simpl in *.
  assert (forall i, ✓{n} (x' !! i) /\ x' !! i ≡{n}≡ (y' ⋅ z) !! i) as Hup'.
  { intros i. destruct (Hup i n (Some (z !! i))); simpl in *.
    - by apply list_lookup_validN.
    - rewrite -list_lookup_op.
      by apply list_dist_lookup.
    - rewrite list_lookup_op. split; done.
  }
  split; [apply list_lookup_validN | apply list_dist_lookup].
  all: intros i; by destruct (Hup' i).
Qed.

Lemma list_app_l_local_update {A: ucmraT}:
  forall (x y y' z: list A),
    (y, ε) ~l~> (y', z) ->
    (x ++ y, ε) ~l~> (x ++ y', (replicate (length x) ε) ++ z).
Proof.
  intros ? ? ? ? HUp.
  apply local_update_unital=> n mz Hxv Hx.
  unfold local_update in HUp. simpl in *.
  specialize (HUp n (Some y)).
  simpl in *.
  move: HUp Hx.
  repeat rewrite ucmra_unit_left_id.
  move=> HUp <-.
  apply list_validN_app in Hxv. destruct Hxv as [Hxv Hyv].
  specialize (HUp Hyv).
  rewrite list_validN_app.
  destruct HUp as [Hy'v Hy'eq].
  auto.
  repeat split; try done.
  rewrite Hy'eq.
  apply list_dist_lookup.
  intros i.
  rewrite list_lookup_op.
  destruct (decide (i < length x)%nat) as [HLt|HGe].
  {
    repeat rewrite lookup_app_l.
    all: (try rewrite replicate_length); try lia.
    2: assumption. (* why doesn't lia work ??? *)
    rewrite lookup_replicate_2; try lia.
    apply lookup_lt_is_Some in HLt.
    destruct HLt as (? & HEl).
    by rewrite HEl -Some_op ucmra_unit_left_id.
  }
  {
    assert (length x <= i)%nat as HLe by lia.
    repeat rewrite lookup_app_r.
    all: try rewrite replicate_length.
    all: try lia.
    2: assumption.
    remember (i - length _)%nat as K. clear.
    by rewrite list_lookup_op.
  }
Qed.

Lemma list_app_r_local_update {A: ucmraT}:
  forall (x x' y y': list A),
    length x = length x' ->
    (x, ε) ~l~> (x', y') ->
    (x ++ y, ε) ~l~> (x' ++ y, y').
Proof.
  intros ? ? ? ? HLen HUp.
  apply local_update_unital=> n mz Hxv.
  rewrite ucmra_unit_left_id. move=> <-.
  specialize (HUp n (Some x)); simpl in *.
  apply list_validN_app in Hxv. destruct Hxv as [Hxv Hyv].
  destruct HUp as [Hx'v Hx'Eq]; auto.
  split.
  by apply list_validN_app.
  rewrite Hx'Eq.
  assert (length y' <= length x)%nat as Hy'Len.
  {
    assert (length x = length (y' ⋅ x)) as ->.
    by rewrite -Hx'Eq.
    rewrite list_length_op.
    lia.
  }
  symmetry.
  rewrite mixin_cmra_comm.
  rewrite list_op_app_le.
  rewrite mixin_cmra_comm.
  all: try done.
  apply list_cmra_mixin.
  apply list_cmra_mixin.
Qed.

Lemma ucmra_cancel_local_update {A: ucmraT} (x: A) `{!Cancelable x}:
  (x, x) ~l~> (ε, ε).
Proof.
  intros n f ? Heq. split; first by apply ucmra_unit_validN.
  apply (cancelableN x); rewrite /= ucmra_unit_right_id; first done.
  destruct f as [f'|]; simpl in *.
  by rewrite ucmra_unit_left_id.
  by rewrite ucmra_unit_right_id.
Qed.
