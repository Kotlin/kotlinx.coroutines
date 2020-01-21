From iris.heap_lang Require Import proofmode notation lang.
From iris.algebra Require Import cmra auth list agree csum excl gset frac.

Theorem elem_of_map {A B} {f: A -> B} (l: list A) x:
  x ∈ f <$> l -> (exists y, y ∈ l /\ x = f y).
Proof.
  intros Hel.
  destruct l; first by inversion Hel.
  simpl in Hel.
  remember (f a :: list_fmap A B f l) as l'.
  generalize dependent l.
  generalize dependent a.
  induction Hel as [|x ? l'' Hel]; intros; inversion Heql'; subst; simpl in *.
  - exists a; split; econstructor.
  - destruct l; first by inversion Hel.
    simpl in *.
    destruct (IHHel _ _ eq_refl) as [y' [Hy'el Hy'eq]]; subst.
    eexists _; split; by econstructor.
Qed.

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
    (x, y) ~l~> (list_alter f n x, list_alter g n y).
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
  intros ? ? ? n mz _ Heq. exfalso. simpl in *.
  symmetry in Heq. apply (dist_None n _) in Heq.
  destruct mz; simpl in Heq.
  1: rewrite Some_op_opM in Heq.
  all: discriminate.
Qed.

Lemma map_lookup: forall {A B: Type} (f: A -> B) l i, map f l !! i = option_map f (l !! i).
Proof. induction l; destruct i; simpl; auto. Qed.

Lemma big_opL_forall' {M: ofeT} {o: M -> M -> M} {H': Monoid o} {A B: Type}
      R f g (l: list A) (l': list B):
  Reflexive R ->
  Proper (R ==> R ==> R) o ->
  length l = length l' ->
  (forall k y y', l !! k = Some y -> l' !! k = Some y' -> R (f k y) (g k y')) ->
  R ([^o list] k ↦ y ∈ l, f k y) ([^o list] k ↦ y ∈ l', g k y).
Proof.
  intros ??. revert l' f g. induction l as [|x l IH]=> l' f g HLen HHyp //=.
  all: destruct l'; inversion HLen; eauto.
  simpl. f_equiv; eauto.
Qed.

Lemma big_sepL_forall_2 {PROP: bi} {A B: Type}
      (f: nat -> A -> PROP) (g: nat -> B -> PROP)
      (l: list A) (l': list B):
  strings.length l = strings.length l' ->
  (∀ (k : nat) y y', l !! k = Some y → l' !! k = Some y' → f k y ≡ g k y') ->
  ([∗ list] k ↦ y ∈ l, f k y)%I ≡ ([∗ list] k ↦ y ∈ l', g k y)%I.
Proof. intros. apply big_opL_forall'; eauto; try apply _. Qed.

Lemma big_sepL_list_alter {PROP: bi} {A: Type} {P: nat -> A -> PROP} (f: A -> A) v i x':
  v !! i = Some x' ->
  ([∗ list] k ↦ x ∈ v, P k x) -∗
  (P i (f x')) -∗
  (P i x' ∗ [∗ list] k ↦ x ∈ alter f i v, P k x).
Proof.
  iIntros (?) "HList HVal".
  assert (i < length v)%nat as HLength by (apply lookup_lt_is_Some_1; eauto).
  assert (i = (length (take i v) + 0)%nat) as HCidLen.
  { rewrite take_length_le. by rewrite -plus_n_O. lia. }
  replace (alter _ i) with (@alter _ _ _ list_alter f (length (take i v) + 0)%nat) by auto.
  remember (length _ + 0)%nat as K.
  replace v with (take i v ++ x' :: drop (S i) v) by (rewrite take_drop_middle; auto).
  subst K.
  rewrite alter_app_r.
  rewrite big_opL_app. rewrite big_opL_app. simpl.
  iDestruct "HList" as "[HListPre [HListMid HListSuf]]".
  rewrite -HCidLen.
  by iFrame.
Qed.

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

Lemma replicate_op {A: ucmraT} (a b: A) n:
  replicate n (a ⋅ b) = replicate n a ⋅ replicate n b.
Proof. apply list_eq. induction n; simpl. done. case; done. Qed.

Lemma pair_op_2 {A: ucmraT} {B: cmraT} (b b': B):
  (ε, b ⋅ b') ≡ ((ε: A), b) ⋅ (ε, b').
Proof. by rewrite -pair_op ucmra_unit_left_id. Qed.

Lemma big_opL_irrelevant_element (M: ofeT) (o: M -> M -> M) (H': Monoid o)
      {A: Type} n (P: nat -> M) (l: list A):
  ([^o list] i ↦ _ ∈ l, P (n+i)%nat)%I =
  ([^o list] i ∈ seq n (length l), P i%nat)%I.
Proof.
  assert (length l = length (seq n (length l))) as HSeqLen
      by (rewrite seq_length; auto).
  apply big_opL_forall'; try apply _. done.
  intros ? ? ? _ HElem.
  assert (k < length l)%nat as HKLt.
  { rewrite HSeqLen. apply lookup_lt_is_Some. by eexists. }
  apply nth_lookup_Some with (d:=O) in HElem.
  rewrite seq_nth in HElem; subst; done.
Qed.

Lemma big_opL_replicate_irrelevant_element
      (M: ofeT) (o: M -> M -> M) (H': Monoid o)
      {A: Type} (P: nat -> A -> M) (a: A) n:
  ([^o list] i ↦ k ∈ replicate n a, P i k)%I =
  ([^o list] i ↦ _ ∈ replicate n a, P i a)%I.
Proof.
  apply big_opL_gen_proper; try apply _.
  intros ? ?; rewrite lookup_replicate; case; by intros ->.
Qed.

Lemma big_opL_irrelevant_element'
      (M: ofeT) (o: M -> M -> M) (H': Monoid o)
      {A: Type} (P: nat -> M) (l: list A):
  ([^o list] i ↦ k ∈ l, P i)%I = ([^o list] i ∈ seq 0 (length l), P i%nat)%I.
Proof. by rewrite -big_opL_irrelevant_element. Qed.

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

  apply Vector.eq_nth_iff.
  intros ? p ->.
  rewrite HEq.
  symmetry.
  apply Vector.const_nth.
Qed.

Lemma local_update_refl {A: cmraT}: forall (a b: A),
  (a, b) ~l~> (a, b).
Proof.
  intros. unfold local_update. intros. simpl in *. split; done.
Qed.

Lemma seq_add: forall m n k,
    seq n (m + k)%nat = seq n m ++ seq (n + m)%nat k.
Proof.
  induction m; simpl; intros; first by rewrite Nat.add_0_r.
  congr (cons n). replace (n + S m)%nat with (S n + m)%nat by lia.
  by apply IHm.
Qed.

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

Lemma pair_op_1 {A: ucmraT} {B: cmraT} (b b': B):
  (b ⋅ b', ε) ≡ (b, (ε: A)) ⋅ (b', (ε: A)).
Proof. by rewrite -pair_op ucmra_unit_left_id. Qed.

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

Fixpoint count_matching {A} (P: A -> Prop) {H': forall x, Decision (P x)} (l: list A): nat :=
  match l with
  | nil => 0
  | cons x l' => if decide (P x) then S (count_matching P l') else count_matching P l'
  end.

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

Theorem count_matching_is_sum
        {A} (P: A -> Prop) {H': forall x, Decision (P x)}:
  forall l,
  let to_nat x := if decide (P x) then 1%nat else 0%nat in
  count_matching P l = foldr (fun v a => a + to_nat v)%nat O l.
Proof.
  rewrite /count_matching /filter. induction l; rewrite /= //.
  destruct (decide (P a)); rewrite /= IHl /=; lia.
Qed.

Theorem count_matching_alter
        {A} (P: A -> Prop) {H': forall x, Decision (P x)}:
  let to_num x := if decide (P x) then 1%nat else 0%nat in
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

Lemma included_None {A: cmraT} (a : option A):
  (a ≼ None) -> a = None.
Proof.
  rewrite option_included. case; first done.
  intros (? & ? & _ & HContra & _). discriminate.
Qed.

Lemma list_lookup_singletonM_lt:
    forall (A: ucmraT) (i i': nat) (x: A),
                (i' < i)%nat -> list_singletonM i x !! i' = Some (ε: A).
Proof.
  induction i; intros [|i']; naive_solver auto with lia.
Qed.

Lemma list_lookup_singletonM_gt:
    forall (A: ucmraT) (i i': nat) (x: A),
                (i < i')%nat -> list_singletonM i x !! i' = None.
Proof.
  induction i; intros [|i']; naive_solver auto with lia.
Qed.

Lemma None_least (A: cmraT) (a: option A): None ≼ a.
Proof. by apply option_included; left. Qed.

Lemma list_singletonM_included {A: ucmraT} (i: nat) (x: A) (l: list A):
  {[i := x]} ≼ l <-> (exists v, l !! i = Some v ∧ x ≼ v).
Proof.
  rewrite list_lookup_included.
  split.
  {
    intros HEv. specialize (HEv i). move: HEv.
    rewrite list_lookup_singletonM. destruct (l !! i) as [x'|].
    2: by intros HContra; apply included_None in HContra.
    rewrite Some_included_total. eauto.
  }
  {
    intros (v & HEl & HInc) i'.
    destruct (decide (i < i')%nat).
    {
      rewrite list_lookup_singletonM_gt //.
      apply None_least.
    }
    destruct (decide (i = i')%nat).
    {
      subst.
      rewrite list_lookup_singletonM. rewrite HEl.
      by apply Some_included_total.
    }
    {
      rewrite list_lookup_singletonM_lt; last lia.
      assert (i < length l)%nat.
      by apply lookup_lt_is_Some; eauto.
      assert (is_Some (l !! i')) as [? HEl'].
      by apply lookup_lt_is_Some; lia.
      rewrite HEl' Some_included_total.
      apply ucmra_unit_least.
    }
  }
Qed.

Fixpoint find_index {A} (P: A -> Prop) {H': forall x, Decision (P x)}
         (l: list A): option nat :=
  match l with
  | nil => None
  | cons x l => if decide (P x) then Some 0%nat
               else option_map S (find_index P l)
  end.

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

Theorem prod_included':
  forall (A B: cmraT) (x y: (A * B)), x.1 ≼ y.1 ∧ x.2 ≼ y.2 -> x ≼ y.
Proof.
    by intros; apply prod_included.
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
  rewrite -minus_Sn_m. auto.
  apply count_matching_le_length.
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
  { symmetry. rewrite drop_app_le. rewrite drop_ge. done. all: lia. }
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
  rewrite present_cells_in_take_1_drop_i_if_next_present_is_Si.
  rewrite present_cells_in_take_i_if_next_present_is_Si.
  all: try done.
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

Lemma big_sepL_lookup_alter {PROP: bi} {A: Type} i s f (P: nat -> A -> PROP) (l: list A) v:
  l !! i = Some v ->
  ([∗ list] i ↦ k ∈ l, P (s+i)%nat k) -∗
  (P (s+i)%nat v ∗ (P (s+i)%nat (f v) -∗
                      [∗ list] i ↦ k ∈ (alter f i l), P (s+i)%nat k)).
Proof.
  iIntros (HEl) "HList".
  iInduction l as [|x l'] "IH" forall (s i HEl); first by inversion HEl.
  destruct i; simpl in *.
  - inversion HEl; subst.
    rewrite Nat.add_0_r. iDestruct "HList" as "[$ $]".
    by iIntros "$".
  - iDestruct "HList" as "[$ HList]".
    rewrite -plus_n_Sm.
    iDestruct ("IH" $! (S s) i HEl with "[HList]") as "[$ HLst] /=".
    { iDestruct (big_sepL_mono with "HList") as "$".
      iIntros (? ? ?) "HAp". by rewrite -plus_n_Sm. }
    iIntros "HPs". iDestruct ("HLst" with "HPs") as "HLst".
    iDestruct (big_sepL_mono with "HLst") as "$".
    iIntros (? ? ?) "HAp". by rewrite -plus_n_Sm.
Qed.

Lemma big_sepL_lookup_alter_abort {PROP: bi} {A: Type} i s f (P: nat -> A -> PROP) (l: list A) v:
  l !! i = Some v ->
  ([∗ list] i ↦ k ∈ l, P (s+i)%nat k) -∗
  (P (s+i)%nat v ∗ ((P (s+i)%nat v -∗ [∗ list] i ↦ k ∈ l, P (s+i)%nat k) ∧
                    (P (s+i)%nat (f v) -∗
                       [∗ list] i ↦ k ∈ (alter f i l), P (s+i)%nat k))).
Proof.
  iIntros (HEl) "HList".
  iInduction l as [|x l'] "IH" forall (s i HEl); first by inversion HEl.
  destruct i; simpl in *.
  - inversion HEl; subst.
    rewrite Nat.add_0_r. iDestruct "HList" as "[$ $]".
    iSplit; by iIntros "$".
  - iDestruct "HList" as "[$ HList]".
    rewrite -plus_n_Sm.
    iDestruct ("IH" $! (S s) i HEl with "[HList]") as "[$ HLst] /=".
    { iDestruct (big_sepL_mono with "HList") as "$".
      iIntros (? ? ?) "HAp". by rewrite -plus_n_Sm. }
    iSplit; iIntros "HPs".
    1: iDestruct "HLst" as "[HLst _]".
    2: iDestruct "HLst" as "[_ HLst]".
    all: iDestruct ("HLst" with "HPs") as "HLst".
    all: iDestruct (big_sepL_mono with "HLst") as "$".
    all: iIntros (? ? ?) "HAp". all: by rewrite -plus_n_Sm.
Qed.

Lemma None_op_left_id {A: cmraT} (a: option A): None ⋅ a = a.
Proof. rewrite /op /cmra_op /=. by destruct a. Qed.

Theorem prod_included'':
  forall (A B: cmraT) (x y: (A * B)), x ≼ y -> x.1 ≼ y.1 ∧ x.2 ≼ y.2.
Proof.
    by intros; apply prod_included.
Qed.

Theorem prod_included''':
  forall (A B: cmraT) (x x' : A) (y y': B), (x, y) ≼ (x', y') -> x ≼ x' ∧ y ≼ y'.
Proof.
  intros ? ? ? ? ? ? HEv.
  apply prod_included'' in HEv.
  by simpl in *.
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

Lemma list_validN_app {A: ucmraT} (x y : list A) (n: nat):
  ✓{n} (x ++ y) <-> ✓{n} x ∧ ✓{n} y.
Proof. apply Forall_app. Qed.

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
    rewrite list_op_length.
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

Lemma nat_lt_sum (x y: nat):
  (x < y)%nat <-> (exists z, y = x + S z)%nat.
Proof.
  rewrite -Nat.le_succ_l nat_le_sum /=.
  split; case; intros ? ->; eexists; by rewrite -plus_n_Sm.
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

Lemma quot_of_nat n m:
  Z.of_nat n `quot` Z.of_nat m = Z.of_nat (n `div` m).
Proof.
  destruct m. destruct n; done.
  rewrite Z2Nat_inj_div; apply Z.quot_div_nonneg; lia.
Qed.

Lemma rem_of_nat n m:
  Z.of_nat n `rem` Z.of_nat (S m) = Z.of_nat (n `mod` S m).
Proof.
  rewrite Z2Nat_inj_mod; apply Z.rem_mod_nonneg; lia.
Qed.

Theorem count_matching_find_index_Some A (P: A -> Prop) (H': forall x, Decision (P x)) l:
  (count_matching P l > 0)%nat -> is_Some (find_index P l).
Proof.
  induction l; simpl; first lia.
  destruct (decide (P a)); first by eauto.
  destruct (find_index P l); by eauto.
Qed.
