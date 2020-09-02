From iris.heap_lang Require Import proofmode.

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
  length l = length l' ->
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

Lemma big_opL_take_drop_middle (M: ofeT) (o : M → M → M) (H': Monoid o) (A: Type)
      (f: nat → A → M) (l: list A) (id: nat) (x: A):
  l !! id = Some x →
  ([^o list] k ↦ y ∈ l, f k y) ≡
    (o ([^o list] k ↦ y ∈ take id l, f k y)
       (o (f id x) ([^o list] k ↦ y ∈ drop (S id) l, f (id + S k) y))).
Proof.
  intros HEl.
  erewrite <-(take_drop_middle l); last done.
  assert (id < length l)%nat by (eapply lookup_lt_Some; eassumption).
  rewrite big_opL_app take_app_alt.
  rewrite drop_app_ge.
  all: rewrite take_length_le //=; try lia.
  replace (S id - id)%nat with 1 by lia. simpl.
  by rewrite drop_0 Nat.add_0_r.
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

From iris.algebra Require Import cmra gset numbers.

Lemma big_opL_op_prodR r (A B : ucmraT) (C : Type)
      (f : nat → C → A) (g : nat → C → B) (l : list C):
  ([^op list] k↦x ∈ l, ((f (r + k) x, g (r + k) x) : prodR A B)) ≡
  (([^op list] k↦x ∈ l, f (r + k) x), ([^op list] k↦x ∈ l, g (r + k) x)).
Proof.
  generalize dependent r.
  induction l as [|v l']=> //= r.
  setoid_rewrite <-plus_n_Sm.
  by rewrite Nat.add_0_r pair_op (IHl' (S r)).
Qed.

Lemma big_opL_op_ucmra_unit (A: ucmraT) (C : Type) (l : list C):
  ([^op list] _ ∈ l, (ε: A)) ≡ ε.
Proof. induction l=>//=. rewrite IHl ucmra_unit_left_id //. Qed.

Lemma big_opL_op_gset n m:
  GSet (set_seq n m) ≡ [^op list] x ∈ seq n m, GSet {[x]}.
Proof.
  move: m n. elim=> //= m IHm n. rewrite -(IHm (S n)).
  rewrite -gset_op_union gset_disj_union //=.
  apply set_seq_S_start_disjoint.
Qed.

Global Instance max_monoid: Monoid max.
Proof.
  apply (Build_Monoid natO max 0)=> //; try apply _.
  - intros x y z. rewrite leibniz_equiv_iff. apply Max.max_assoc.
  - intros x y. rewrite leibniz_equiv_iff. apply Max.max_comm.
Defined.

Global Instance max_nat_homomorphism:
  MonoidHomomorphism max op equiv MaxNat.
Proof.
  econstructor; last done.
  econstructor; try apply _.
  intros. by rewrite max_nat_op_max.
Qed.

Lemma big_opL_op_max_nat {A: Type} (f: nat → A -> max_natR) (l: list A):
  MaxNat ([^max list] k ↦ x ∈ l, max_nat_car (f k x)) ≡
  ([^op list] k ↦ x ∈ l, f k x).
Proof.
  rewrite (big_opL_commute _). apply big_opL_proper. intros. by destruct (f _ _).
Qed.

Lemma big_opL_op_nat {A: Type} (f: nat → A -> natR) (l: list A):
  ([^Nat.add list] k ↦ x ∈ l, f k x) ≡
  ([^op list] k ↦ x ∈ l, f k x).
Proof. done. Qed.

Lemma big_opL_op_nat' {A: Type} (i: nat) (l: list A):
  length l * i ≡ ([^op list] k ↦ x ∈ l, i).
Proof. induction l=> //=. by rewrite IHl. Qed.
