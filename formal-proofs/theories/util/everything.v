From iris.heap_lang Require Import proofmode notation lang.
From iris.algebra Require Import cmra auth list agree csum excl gset frac numbers.

Lemma map_lookup: forall {A B: Type} (f: A -> B) l i, map f l !! i = option_map f (l !! i).
Proof. intros. apply list_lookup_fmap. Qed.

Lemma VectorDef_replace_order_list_alter: forall A n r (p: (r < n)%nat) x (v: vec A n),
               vec_to_list (VectorDef.replace_order v p x) = alter (fun _ => x) r (vec_to_list v).
Proof.
  intros. generalize dependent r. induction v; simpl.
  - inversion p.
  - intros. destruct r; simpl; auto.
    unfold alter in IHv.
    rewrite -(IHv _ (lt_S_n r n p)).
    done.
Qed.

Lemma list_filter_length_le {A} p (l: list A):
  length (List.filter p l) <= length l.
Proof.
  induction l; simpl. lia. destruct (p a); simpl; lia.
Qed.

Lemma list_filter_length_eq {A} p (l: list A):
  length (List.filter p l) = length l -> List.filter p l = l.
Proof.
  intros Hll. induction l as [|r l']; simpl in *; first by auto.
  destruct (p r) eqn:E; simpl in *.
  2: assert (length (List.filter p l') <= length l')
    by apply list_filter_length_le; lia.
  congr (r :: _). auto.
Qed.

Lemma list_filter_length_eq_in {A} p (l: list A):
  length (List.filter p l) = length l -> forall i, In i l -> p i.
Proof.
  intros HLL. apply list_filter_length_eq in HLL.
  rewrite <- HLL.
  intros i HIn.
  apply filter_In in HIn.
  destruct HIn. auto.
Qed.

Lemma filter_induces_vector:
  forall v (cells : vec bool v), v = length (List.filter (fun x => x) cells) ->
           cells = Vector.const true v.
Proof.
  intros v cells HH.
  assert (forall f, cells !!! f = true) as HEq.
  {
    intros f. destruct (cells !!! f) eqn:E; auto.
    assert (exists f, cells !!! f = false) as HContra by eauto.
    move: HContra. rewrite -elem_of_vlookup elem_of_list_In. move=> HEl.
    assert (length (List.filter (fun i => i) (vec_to_list cells)) =
            length (vec_to_list cells)) as HLen.
    by rewrite vec_to_list_length.
    eapply list_filter_length_eq_in in HLen.
    2: apply HEl.
    inversion HLen.
  }

  apply vec_eq.
  intros ?.
  rewrite HEq.
  symmetry.
  clear. by induction i.
Qed.

Lemma seq_add: forall m n k,
    seq n (m + k)%nat = seq n m ++ seq (n + m)%nat k.
Proof. intros. apply List.seq_app. Qed.

Lemma seq_app: forall m n k, (m <= k)%nat ->
    seq n m ++ seq (n + m)%nat (k - m)%nat = seq n k.
Proof.
  intros m n k HLt.
  replace k with (m + (k - m))%nat by lia.
  rewrite seq_add. replace (m + (k - m) - m)%nat with (k - m)%nat by lia.
  done.
Qed.

Lemma seq_bind n m k:
  seq n m ≫= (fun x => seq (x * k) k) = seq (n * k) (m * k).
Proof.
  unfold mbind.
  generalize dependent n.
  induction m; simpl; first done.
  intros. rewrite seq_add IHm. simpl.
  replace (k + n * k)%nat with (n * k + k)%nat by lia.
  done.
Qed.

Theorem filter_app {A} (P: A -> Prop) {H': forall x, Decision (P x)} (l1 l2: list A):
  filter P (l1 ++ l2) = filter P l1 ++ filter P l2.
Proof.
  unfold filter. induction l1; rewrite /= // /filter. rewrite IHl1.
  by destruct (decide (P a)).
Qed.

Theorem filter_List_filter_compatible {A} (P: A -> bool) (l: list A):
  filter P l = List.filter P l.
Proof.
  rewrite /filter. induction l; rewrite /= //.
  rewrite -IHl. by destruct (P a).
Qed.

Lemma drop_alter' {A} (f: A -> A) n i (l: list A):
  drop n (alter f (n+i)%nat l) = alter f i (drop n l).
Proof.
  revert n.
  induction l; first by case.
  case; first done.
  auto.
Qed.

Lemma take_drop_middle_alter A (l: list A) (i: nat) f (x: A):
  l !! i = Some x ->
  alter f i l = take i l ++ (f x :: drop (S i) l).
Proof.
  intros HEl.
  assert (i < length l)%nat by (apply lookup_lt_is_Some; eauto).

  apply list_eq. intros j.
  destruct (decide (i = j)).
  {
    subst. rewrite list_lookup_alter HEl /=.
    rewrite lookup_app_r take_length_le; try lia.
    by rewrite minus_diag //.
  }
  {
    rewrite list_lookup_alter_ne //.
    destruct (decide (i < j)%nat).
    {
      rewrite lookup_app_r take_length_le; try lia.
      destruct (j - i)%nat eqn:E; first by lia.
      simpl.
      rewrite lookup_drop /= plus_n_Sm -E.
      replace (i + (j - i))%nat with j by lia.
      done.
    }
    {
      rewrite lookup_app_l. 2: rewrite take_length_le; try lia.
      rewrite lookup_take //. lia.
    }
  }
Qed.

Lemma fmap_is_map {A B} (f: A -> B) (l: list A): f <$> l = map f l.
Proof. auto. Qed.

Lemma nat_lt_sum (x y: nat):
  (x < y)%nat <-> (exists z, y = x + S z)%nat.
Proof.
  rewrite -Nat.le_succ_l nat_le_sum /=.
  split; case; intros ? ->; eexists; by rewrite -plus_n_Sm.
Qed.

Lemma quot_of_nat n m:
  Z.quot (Z.of_nat n) (Z.of_nat m) = Z.of_nat (n `div` m)%nat.
Proof.
  destruct m. destruct n; done.
  rewrite Nat2Z_inj_div; apply Z.quot_div_nonneg; lia.
Qed.

Lemma rem_of_nat n m:
  Z.rem (Z.of_nat n) (Z.of_nat (S m)) = Z.of_nat (n `mod` S m).
Proof.
  rewrite Nat2Z_inj_mod; apply Z.rem_mod_nonneg; lia.
Qed.

Lemma rem_of_nat' n m:
  m > 0 →
  Z.rem (Z.of_nat n) (Z.of_nat m) = Z.of_nat (n `mod` m).
Proof. intros ?. destruct m; first lia. apply rem_of_nat. Qed.
