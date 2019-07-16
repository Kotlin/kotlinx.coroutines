From iris.base_logic.lib Require Export invariants.
From iris.proofmode Require Import tactics.
From iris.heap_lang Require Import proofmode notation lang.
From iris.program_logic Require Export weakestpre atomic.
From iris.algebra Require Import cmra auth excl vector list.
Require Import SegmentQueue.lib.array.array_spec.
Require Import SegmentQueue.lib.array.array_impl.

Class arrayG Σ :=
  ArrayG {
      array_tokG :> inG Σ (authR (optionUR (exclR (listO valO))))
    }.

Definition arrayΣ : gFunctors :=
  #[GFunctor (authR (optionUR (exclR (listO valO))))].

Instance subG_arrayΣ {Σ} : subG arrayΣ Σ -> arrayG Σ.
Proof. solve_inG. Qed.

Variable Σ: gFunctors.

Context `{heapG Σ, !arrayG Σ} (N : namespace).

Notation iProp := (iProp Σ).

Fixpoint vector_zip {A B: Type} {n: nat} : vec A n -> vec B n -> vec (A * B) n :=
  match n as i return (vec A i -> vec B i -> vec (A * B) i) with
  | O => fun _ _ => vnil
  | S n' => fun a b => (Vector.hd a, Vector.hd b) ::: vector_zip (Vector.tl a) (Vector.tl b)
  end.

Theorem vector_zip_inv {A B: Type} {n: nat} (a: vec (A * B) n):
  vector_zip (vmap fst a) (vmap snd a) = a.
Proof.
  induction a; auto.
  destruct h as [x y].
  simpl.
  by rewrite -> IHa.
Qed.

Fixpoint array_is (ℓ: loc) {n: nat} (s: vec (val * (loc * loc)) n): iProp :=
  match s with
  | vnil => (ℓ ↦ #())%I
  | ((h, (hℓ, tℓ)) ::: t) => (ℓ ↦ (#hℓ, #tℓ)%V ∗ hℓ ↦ h ∗ array_is tℓ t)%I
  end.

Definition array_inv (γ: gname) (ℓ: loc) {n: nat} (locs: vec (loc * loc) n) : iProp :=
  (∃ (v : vec val n), own γ (● Excl' (vec_to_list v)) ∗ array_is ℓ (vector_zip v locs))%I.

Definition is_array (γ: gname) (v: val) (n: nat): iProp :=
  (∃ (ℓ: loc) (locs: vec (loc * loc) n), ⌜v = #ℓ⌝ ∧ inv N (array_inv γ ℓ locs))%I.

Definition array_content (γ : gname) {m: nat} (v: vec val m) : iProp :=
  own γ (◯ Excl' (vec_to_list v)).

Global Instance is_array_persistent (γ: gname) (v: val) (n : nat):
  Persistent (is_array γ v n).
Proof. apply _. Qed.

Theorem new_array_spec (k: nat) (v: val):
  {{{ True }}}
    make_array #k v
  {{{ γs s, RET s; is_array γs s k ∗ array_content γs (VectorDef.const v k) }}}.
Proof.
  assert (
    {{{ True }}}
      make_array #k v
    {{{ γs s (ℓ: loc) (vc: vec (val * (loc * loc)) k), RET s;
        ⌜s = #ℓ⌝ ∧
        own γs (● Excl' (vec_to_list (Vector.map fst vc))) ∗
        @array_is ℓ _ vc ∗
        array_content γs (VectorDef.const v k)
    }}}) as HEv.
  {
    induction k as [|k']; iIntros (Φ) "_ HPost"; rewrite /make_array -wp_fupd; wp_pures.
    {
      iMod (own_alloc (● Excl' (vec_to_list (@vnil val)) ⋅
                         ◯ Excl' (vec_to_list (@vnil val)))) as (γs) "HOwn".
      { apply auth_both_valid. split; done. }
      replace (@vnil val) with (@vmap (val * (loc * loc)) _ fst _ vnil) by auto.
      rewrite own_op.
      iDestruct "HOwn" as "[HAuth HFrag]".
      wp_alloc hd as "HAll".
      iApply ("HPost" $! γs).
      iModIntro.
      iFrame; simpl.
      iFrame.
      auto.
    }
    {
      wp_bind (ref v)%E.
      wp_alloc hd as "HHead".
      wp_let.
      fold make_array.
      wp_pure _.
      replace (S k' - 1) with (Z.of_nat k') by lia.
      wp_bind (make_array #k' v)%E.
      wp_apply IHk'; auto.
      iIntros (γs s ℓ vc) "[% [HOwn [HArr HCont]]]".
      wp_pures.
      rewrite /is_array /array_content /array_inv.
      wp_alloc r as "HRes".
      iDestruct (own_valid_2 with "HOwn HCont") as %[H%Excl_included _]%auth_both_valid.
      apply leibniz_equiv in H.
      subst.
      assert (VectorDef.const v k' = (vmap fst vc)). {
        remember (vmap fst vc) as vc'.
        clear dependent vc.
        clear IHk'.
        induction vc'; auto.
        simpl in *.
        inversion H; subst.
        rewrite IHvc'; auto.
      }
      replace (vmap fst vc) with (VectorDef.const v k') by auto.
      clear H.
      iDestruct (own_update_2 with "HOwn HCont") as ">H".
      { eapply auth_update. apply option_local_update.
        eapply (exclusive_local_update _ (Excl (vec_to_list (VectorDef.const v (S k'))))). done. }
      rewrite own_op.
      iDestruct "H" as "[HAuth HFrag]".
      iApply "HPost".
      iModIntro.
      iSplitR; first done.
      simpl.
      replace (VectorDef.const v k') with (vmap fst vc) by auto.
      replace (v :: vmap fst vc) with (vec_to_list (vmap fst ((v, (hd, ℓ)) ::: vc))) by auto.
      iFrame.
    }
  }
  iIntros (Φ) "_ HPost".
  rewrite /make_array -wp_fupd.
  iApply HEv; auto.
  iNext.
  iIntros (? ? ? ?) "[% [HAuth [HArr HCont]]]"; subst.
  iMod (inv_alloc N _ (array_inv a a1 (vmap snd a2)) with "[HAuth HArr]") as "#HInv".
  {
    repeat iExists _; iFrame.
    by rewrite vector_zip_inv.
  }
  unfold is_array.
  iApply "HPost".
  iFrame.
  auto.
Qed.

Theorem array_load_spec γs a (n i : nat):
  is_array γs a n -∗
  <<< ∀ (l : vec val n) (p: (i < n)%nat), @array_content γs n l >>>
    array_load a #i @ ⊤∖↑N
  <<< array_content γs l, RET (Vector.nth l (fin_of_nat p)) >>>.
Proof.
  iIntros "HArray".
  iDestruct "HArray" as (ℓ s) "[% #HInv]"; subst.
  iIntros (Φ) "AU".
  iLöb as "IH" forall (i ℓ n s) "HInv".
  wp_lam.
  wp_let.
  wp_bind (!_)%E.
  iInv N as "HI" "HClose".
  iDestruct "HI" as (vc) "[HAuth HArr]".
  destruct vc.
  {
    iMod "AU" as (? ?) "[HArrCont [_ HCloseAtom]]".
    exfalso.
    lia.
  }
  assert (s = Vector.hd s ::: Vector.tl s) by apply Vector.eta.
  destruct (Vector.hd s) as [hℓ tℓ].
  remember (Vector.tl s) as s'.
  simpl in s'.
  clear Heqs'.
  subst.
  simpl.
  iDestruct "HArr" as "[Hℓ HArr]".
  wp_load.
  iMod ("HClose" with "[Hℓ HArr HAuth]") as "_".
  {
    iNext. iExists (h ::: vc). iFrame.
  }
  iModIntro.
  wp_pures.
  wp_bind (!_)%E.
  iInv N as "HI" "HClose".
  iDestruct "HI" as (vc') "[HAuth HArr]".
  simpl.
  iDestruct "HArr" as "[Hℓ HArr]".
  wp_load.
  iMod ("HClose" with "[Hℓ HArr HAuth]") as "_".
  {
    iNext. iExists _. iFrame.
  }
  iModIntro.
  wp_pures.
  destruct i; simpl; wp_pures.
  2: replace (S i - 1)%Z with (Z.of_nat i) by lia.
  {
    iInv N as "HI" "HClose".
    clear vc vc'.
    iDestruct "HI" as (vc) "[HAuth HArr]".
    simpl.
    iDestruct "HArr" as "[Hℓ [Hhℓ HArrIs]]".
    wp_load.
    iMod "AU" as (l p) "[HArrCont [_ HCloseAtom]]".
    unfold array_content.
    iDestruct (own_valid_2 with "HAuth HArrCont") as
        %[->%Excl_included%leibniz_equiv%vec_to_list_inj2 _]%auth_both_valid.
    iMod ("HCloseAtom" with "HArrCont") as "HΦ".
    iMod ("HClose" with "[Hℓ Hhℓ HAuth HArrIs]") as "_".
    {
      iExists _; iFrame.
    }
    assert (vc = Vector.hd vc ::: Vector.tl vc) by apply Vector.eta.
    rewrite H0.
    simpl.
    auto.
  }
Admitted.
