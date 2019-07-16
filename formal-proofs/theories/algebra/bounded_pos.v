From iris.algebra Require Import cmra.

Section bounded_pos_cmra.
  Inductive bounded_pos := bpos : positive -> positive -> bounded_pos.
  Canonical Structure boundedPosRAC := leibnizO bounded_pos.

  Instance bounded_pos_valid : Valid bounded_pos :=
    fun x => match x with
          | bpos n b => Pos.ltb n b
          end.
  Instance bounded_pos_pcore : PCore bounded_pos :=
    fun _ => None.
  Instance bounded_pos_op : Op bounded_pos :=
    fun x y => match (x, y) with
            | (bpos n1 b1, bpos n2 b2) => bpos (n1 + n2) (Pos.min b1 b2)
            end.

  Lemma bounded_pos_ra_mixin : RAMixin bounded_pos.
  Proof.
    split; try (by eauto; solve_proper); intros [] [];
      rewrite /op /bounded_pos_op.
    - intros [].
      by rewrite Pos.add_assoc; rewrite Pos.min_assoc.
    - by rewrite Pos.add_comm; rewrite Pos.min_comm.
    - intro H.
      apply Is_true_eq_true in H.
      apply Is_true_eq_left.
      apply Pos.ltb_lt in H.
      apply Pos.ltb_lt.
      lia.
  Qed.

  Canonical Structure boundedPosR : cmraT :=
    discreteR bounded_pos bounded_pos_ra_mixin.

  Global Instance bounded_pos_cmra_discrete : CmraDiscrete boundedPosR.
  Proof. apply discrete_cmra_discrete. Qed.

  Lemma bpos_split : forall n m p, bpos (n + m) p = bpos n p ⋅ bpos m p.
  Proof.
    unfold op; unfold cmra_op; simpl; unfold bounded_pos_op.
    intros.
    by rewrite Pos.min_id.
  Qed.

End bounded_pos_cmra.
