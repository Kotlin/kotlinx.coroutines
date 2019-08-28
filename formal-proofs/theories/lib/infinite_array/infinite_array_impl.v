From iris.heap_lang Require Import proofmode notation lang.
Require Import SegmentQueue.lib.util.getAndSet.
Require Import SegmentQueue.lib.util.interruptibly.

Section impl.

Variable segment_size : positive.

Definition new_segment : val :=
  λ: "id" "prev", ref ((("id", ref #0), AllocN #(Zpos segment_size) NONE),
                       (ref "prev", ref NONE)).

Definition segment_id : val :=
  λ: "seg", Fst (Fst (Fst !"seg")).

Definition segment_cancelled : val :=
  λ: "seg", Snd (Fst (Fst !"seg")).

Definition segment_prev : val :=
  λ: "seg", Fst (Snd !"seg").

Definition segment_next : val :=
  λ: "seg", Snd (Snd !"seg").

Definition segment_data_at : val :=
  λ: "seg" "idx", Snd (Fst !"seg") +ₗ "idx".

Definition copy_segment_ref : val :=
  λ: "v", "v".

Definition segment_is_removed : val :=
  λ: "seg", ! (segment_cancelled "seg") = #(Zpos segment_size).

Definition from_some : val :=
  λ: "v", match: "v" with NONE => ! #0 | SOME "v'" => "v'" end.

Definition segment_move_next_to_right : val :=
  rec: "loop" "seg" "next" := let: "curNext" := ! (segment_next "seg") in
                              if: (segment_id (from_some "next") ≤
                                   segment_id (from_some "curNext")) ||
                                  CAS (segment_next "seg") "curNext" "next"
                              then #() else "loop" "seg" "next".

Definition segment_move_prev_to_left : val :=
  rec: "loop" "seg" "prev" := let: "curPrev" := ! (segment_prev "seg") in
                              if: ("curPrev" = NONE) ||
                                  (((("prev" = NONE) = #false) &&
                                  (segment_id (from_some "curPrev") ≤
                                             segment_id (from_some "prev"))) ||
                                  CAS (segment_prev "seg") "curPrev" "prev")
                              then #() else "loop" "seg" "prev".

Definition segment_remove_first_loop : val :=
  rec: "loop" "prev" "next" :=
              if: !"prev" = NONEV
                then #() else
              let: "seg" := from_some ! "prev" in
              segment_move_next_to_right "seg" ! "next" ;;
              if: segment_is_removed "seg" = #false
                then #() else
              "prev" <- !(segment_prev "seg") ;;
              "loop" "prev" "next".

Definition segment_remove_second_loop : val :=
  rec: "loop" "prev" "next" :=
      let: "seg" := (from_some ! "next") in
      if: (segment_is_removed "seg" = #false) ||
          (!(segment_next "seg") = NONE)
      then #() else
      "next" <- !(segment_next "seg") ;;
      segment_move_prev_to_left (from_some ! "next") ! "prev" ;;
      "loop" "prev" "next".

Definition segment_remove : val :=
  λ: "seg", let: "prev" := ref !(segment_prev "seg") in
            let: "next" := ref !(segment_next "seg") in
            if: !"next" = NONEV
              then NONE else
            segment_remove_first_loop "prev" "next" ;;
            segment_move_prev_to_left (from_some ! "next") ! "prev" ;;
            segment_remove_second_loop "prev" "next" ;;
            SOME (!"prev", from_some !"next").

Definition segment_cutoff : val :=
  λ: "seg", (segment_prev "seg") <- NONE.

Definition segment_cancel_cell : val :=
  λ: "seg", FAA (segment_cancelled "seg") #1.

Definition cell_ref_loc : val :=
  λ: "c", let: "seg" := Fst !"c" in
          let: "idx" := Snd !"c" in
          segment_data_at "seg" "idx".

Definition cell_ref_cutoff : val :=
  λ: "c", segment_cutoff (Fst !"c").

Definition new_infinite_array : val :=
  λ: <>, let: "initialSegment" := new_segment #O NONE in
         let: "tail" := "initialSegment" in
         ref ("tail").

Definition array_tail : val :=
  λ: "arr", "arr".

Definition move_tail_forward : val :=
  rec: "loop" "arr" "tail" := let: "curTail" := !(array_tail "arr") in
                              if: segment_id "tail" ≤ segment_id "curTail"
                              then #() else
                                if: CAS (array_tail "arr") "curTail" "tail"
                                then #() else "loop" "arr" "tail".

Definition find_segment : val :=
  rec: "loop" "cur" "fid" :=
    if: "fid" ≤ segment_id "cur" then "cur" else
      let: "next" := ref !(segment_next "cur") in
      (if: ! "next" = NONE then
         let: "newTail" := new_segment (#1%nat + segment_id "cur") (SOME "cur") in
         if: CAS (segment_next "cur") NONE (SOME "newTail") then
           (if: segment_is_removed "cur" then segment_remove "cur" else #()) ;;
           "next" <- SOME "newTail"
         else
           "next" <- !(segment_next "cur")
       else #()) ;;
      "loop" (from_some ! "next") "fid".

End impl.

From iris.algebra Require Import cmra auth list agree csum excl gset frac.

Section proof.

Notation cell_algebra := (optionUR (csumR (agreeR unitO) fracR)).

Notation segment_locations_algebra :=
  (optionUR (agreeR (prodO (prodO locO (prodO locO locO))
                           (prodO locO locO)))).

Notation segment_algebra := (prodUR segment_locations_algebra
                                    (listUR cell_algebra)).

Notation algebra := (authUR (listUR segment_algebra)).

Class iArrayG Σ := IArrayG { iarray_inG :> inG Σ algebra }.
Definition iArrayΣ : gFunctors := #[GFunctor algebra].
Instance subG_iArrayΣ {Σ} : subG iArrayΣ Σ -> iArrayG Σ.
Proof. solve_inG. Qed.

Context `{iArrayG Σ}.
Context `{heapG Σ}.

Notation iProp := (iProp Σ).
Variable (N: namespace).

Variable segment_size : positive.
Variable cell_is_done: nat -> iProp.
Variable cell_is_done_persistent: forall n, Persistent (cell_is_done n).
Variable cell_is_processed: nat -> iProp.
Variable cell_is_processed_persistent: forall n, Persistent (cell_is_processed n).
Variable cell_invariant: gname -> nat -> loc -> iProp.
Variable cell_invariant_persistent: forall γ ℓ n, Persistent (cell_invariant γ n ℓ).

Global Instance list_core_id' {A: ucmraT} (l: listUR A) :
  (forall x, x ∈ l -> CoreId x) -> CoreId l.
Proof.
  intros Hyp. constructor. apply list_equiv_lookup=> i.
  rewrite list_lookup_core.
  destruct (l !! i) eqn:E; rewrite E.
  2: done.
  apply Hyp.
  eapply elem_of_list_lookup; by eauto.
Qed.

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

Section ias_segment_info.

Definition ias_segment_info (id: nat) (s: segment_algebra):
  listUR segment_algebra := replicate id ε ++ [s].

Theorem ias_segment_info_lookup (id: nat) (s: segment_algebra):
  ias_segment_info id s !! id = Some s.
Proof. rewrite /ias_segment_info. induction id; auto. Qed.

Theorem ias_segment_info_alter (id: nat) s f:
  list_alter f id (ias_segment_info id s) = ias_segment_info id (f s).
Proof.
  apply list_eq.
  intros i.
  destruct (nat_eq_dec i id).
  - subst.
    rewrite list_lookup_alter.
    by repeat rewrite ias_segment_info_lookup.
  - rewrite list_lookup_alter_ne; auto.
    rewrite /ias_segment_info.
    generalize dependent i.
    induction id; destruct i; simpl; auto.
    contradiction.
Qed.

Theorem ias_segment_info_op id s s':
  ias_segment_info id (s ⋅ s') =
  ias_segment_info id s ⋅ ias_segment_info id s'.
Proof.
  rewrite /ias_segment_info.
  induction id; simpl.
  2: rewrite IHid.
  all: apply list_eq; case; simpl; trivial.
Qed.

Global Instance ias_segment_info_core_id (id: nat) (s: segment_algebra):
  CoreId s -> CoreId (ias_segment_info id s).
Proof.
  intro SegHyp.
  rewrite /ias_segment_info.
  apply list_core_id'.
  intros ? HElemOf.
  induction id; simpl in *.
  all: inversion HElemOf; subst; first by apply _.
  - exfalso. by eapply not_elem_of_nil.
  - by apply IHid.
Qed.

Theorem ias_segment_info_valid (id: nat) (s: segment_algebra):
  ✓ (ias_segment_info id s) <-> ✓ s.
Proof.
  rewrite /ias_segment_info.
  split.
  - intro Hev.
    induction id; simpl in *; by inversion Hev; auto.
  - intros.
    apply list_lookup_valid.
    induction id; simpl; first by case.
    case; simpl; trivial.
    by compute.
Qed.

End ias_segment_info.

Ltac segment_info_persistent :=
  apply own_core_persistent; apply auth_frag_core_id;
  apply ias_segment_info_core_id; repeat apply pair_core_id; try apply _.

Section ias_cell_info.

Definition ias_cell_info' (id_seg id_cell: nat) (c: cell_algebra):
  listUR segment_algebra :=
  ias_segment_info id_seg (ε, replicate id_cell ε ++ [c]).

Theorem ias_cell_info'_op ns nc s s':
  ias_cell_info' ns nc (s ⋅ s') =
  ias_cell_info' ns nc s ⋅ ias_cell_info' ns nc s'.
Proof.
  rewrite /ias_cell_info'.
  rewrite -ias_segment_info_op.
  congr (ias_segment_info ns).
  rewrite -pair_op.
  replace ((replicate nc ε ++ [s]) ⋅ (replicate nc ε ++ [s']))
          with (replicate nc ε ++ [s ⋅ s']).
  remember (_ ++ _) as k; by compute.
  induction nc; simpl.
  2: rewrite IHnc.
  all: apply list_eq; by case.
Qed.

Global Instance ias_cell_info'_core_id (ids idc: nat) (c: cell_algebra):
  CoreId c -> CoreId (ias_cell_info' ids idc c).
Proof.
  intro CellHyp.
  apply ias_segment_info_core_id.
  apply pair_core_id; first by apply _.
  apply list_core_id'.
  induction idc; intros ? HElemOf; simpl in *.
  all: inversion HElemOf; first by apply _.
  - exfalso. by eapply not_elem_of_nil.
  - by apply IHidc.
Qed.

Theorem ias_cell_info'_valid (ns nc: nat) (s: cell_algebra):
  ✓ (ias_cell_info' ns nc s) <-> ✓ s.
Proof.
  rewrite /ias_cell_info'.
  split.
  - intros Hev.
    apply ias_segment_info_valid in Hev.
    destruct Hev as [_ Hev]. simpl in *.
    induction nc; inversion Hev; by auto.
  - intros. apply ias_segment_info_valid.
    apply pair_valid; split; first by compute.
    apply list_lookup_valid.
    induction nc; case; done.
Qed.

Definition ias_cell_info_view {A: Type} f id: A :=
  let ns := (id `div` Pos.to_nat segment_size)%nat in
  let nc := (id `mod` Pos.to_nat segment_size)%nat in
  f ns nc.

Theorem ias_cell_info_view_eq {A: Type} ns nc n (f: nat -> nat -> A):
  (nc < Pos.to_nat segment_size)%nat ->
  n = (nc + ns * Pos.to_nat segment_size)%nat ->
  f ns nc = ias_cell_info_view f n.
Proof.
  rewrite /ias_cell_info_view.
  intros Hlt Heq. subst.
  replace ((nc + ns * Pos.to_nat segment_size) `div` Pos.to_nat segment_size)%nat
    with ns.
  replace ((nc + ns * Pos.to_nat segment_size) `mod` Pos.to_nat segment_size)%nat
    with nc.
  done.
  { rewrite Nat.mod_add. by rewrite Nat.mod_small.
    assert (O < Pos.to_nat segment_size)%nat by apply Pos2Nat.is_pos; lia. }
  { rewrite Nat.div_add. by rewrite Nat.div_small.
    assert (O < Pos.to_nat segment_size)%nat by apply Pos2Nat.is_pos; lia. }
Qed.

End ias_cell_info.

Ltac cell_info_persistent :=
  apply own_core_persistent; apply auth_frag_core_id;
  apply ias_cell_info'_core_id; repeat apply pair_core_id; try apply _.

Section locations.

Definition segment_locations γ id ℓs: iProp :=
  own γ (◯ (ias_segment_info id (Some (to_agree ℓs), nil))).

Global Instance segment_locations_persistent γ id ℓs:
  Persistent (segment_locations γ id ℓs).
Proof. by segment_info_persistent. Qed.

Theorem segment_locations_agree γ id ℓs ℓs':
  segment_locations γ id ℓs -∗ segment_locations γ id ℓs' -∗ ⌜ℓs = ℓs'⌝.
Proof.
  iIntros "HLoc1 HLoc2".
  iDestruct (own_valid_2 with "HLoc1 HLoc2") as %HValid. iPureIntro.
  revert HValid.
  rewrite auth_frag_valid -ias_segment_info_op ias_segment_info_valid.
  repeat case; simpl; intros.
  by apply agree_op_invL'.
Qed.

Definition segment_location γ id ℓ : iProp :=
  (∃ dℓ cℓ pℓ nℓ, segment_locations γ id (ℓ, (dℓ, cℓ), (pℓ, nℓ)))%I.
Definition segment_data_location γ id dℓ: iProp :=
  (∃ ℓ cℓ pℓ nℓ, segment_locations γ id (ℓ, (dℓ, cℓ), (pℓ, nℓ)))%I.
Definition segment_canc_location γ id cℓ: iProp :=
  (∃ ℓ dℓ pℓ nℓ, segment_locations γ id (ℓ, (dℓ, cℓ), (pℓ, nℓ)))%I.
Definition segment_prev_location γ id pℓ: iProp :=
  (∃ ℓ dℓ cℓ nℓ, segment_locations γ id (ℓ, (dℓ, cℓ), (pℓ, nℓ)))%I.
Definition segment_next_location γ id nℓ: iProp :=
  (∃ ℓ dℓ cℓ pℓ, segment_locations γ id (ℓ, (dℓ, cℓ), (pℓ, nℓ)))%I.

Theorem segment_location_agree γ id ℓ ℓ':
  segment_location γ id ℓ -∗ segment_location γ id ℓ' -∗ ⌜ℓ = ℓ'⌝.
Proof. iIntros "HLoc1 HLoc2".
  iDestruct "HLoc1" as (? ? ? ?) "HLoc1". iDestruct "HLoc2" as (? ? ? ?) "HLoc2".
  iDestruct (segment_locations_agree with "HLoc1 HLoc2") as %HH; iPureIntro.
  revert HH. by intros [=].
Qed.

Theorem segment_data_location_agree γ id ℓ ℓ':
  segment_data_location γ id ℓ -∗ segment_data_location γ id ℓ' -∗ ⌜ℓ = ℓ'⌝.
Proof. iIntros "HLoc1 HLoc2".
  iDestruct "HLoc1" as (? ? ? ?) "HLoc1". iDestruct "HLoc2" as (? ? ? ?) "HLoc2".
  iDestruct (segment_locations_agree with "HLoc1 HLoc2") as %HH; iPureIntro.
  revert HH. by intros [=].
Qed.

Theorem segment_canc_location_agree γ id ℓ ℓ':
  segment_canc_location γ id ℓ -∗ segment_canc_location γ id ℓ' -∗ ⌜ℓ = ℓ'⌝.
Proof. iIntros "HLoc1 HLoc2".
  iDestruct "HLoc1" as (? ? ? ?) "HLoc1". iDestruct "HLoc2" as (? ? ? ?) "HLoc2".
  iDestruct (segment_locations_agree with "HLoc1 HLoc2") as %HH; iPureIntro.
  revert HH. by intros [=].
Qed.

Theorem segment_prev_location_agree γ id ℓ ℓ':
  segment_prev_location γ id ℓ -∗ segment_prev_location γ id ℓ' -∗ ⌜ℓ = ℓ'⌝.
Proof. iIntros "HLoc1 HLoc2".
  iDestruct "HLoc1" as (? ? ? ?) "HLoc1". iDestruct "HLoc2" as (? ? ? ?) "HLoc2".
  iDestruct (segment_locations_agree with "HLoc1 HLoc2") as %HH; iPureIntro.
  revert HH. by intros [=].
Qed.

Theorem segment_next_location_agree γ id ℓ ℓ':
  segment_next_location γ id ℓ -∗ segment_next_location γ id ℓ' -∗ ⌜ℓ = ℓ'⌝.
Proof. iIntros "HLoc1 HLoc2".
  iDestruct "HLoc1" as (? ? ? ?) "HLoc1". iDestruct "HLoc2" as (? ? ? ?) "HLoc2".
  iDestruct (segment_locations_agree with "HLoc1 HLoc2") as %HH; iPureIntro.
  revert HH. by intros [=].
Qed.

Definition segments_mapto γ (locs: list loc): iProp :=
  ([∗ list] id ↦ ℓ ∈ locs, segment_location γ id ℓ)%I.

Global Instance segments_mapto_persistent γ locs:
  Persistent (segments_mapto γ locs).
Proof. apply _. Qed.

End locations.

Hint Extern 1 => match goal with | [ |- context [segment_location]]
                                  => unfold segment_location end.
Hint Extern 1 => match goal with | [ |- context [segment_data_location]]
                                  => unfold segment_data_location end.
Hint Extern 1 => match goal with | [ |- context [segment_canc_location]]
                                  => unfold segment_canc_location end.
Hint Extern 1 => match goal with | [ |- context [segment_prev_location]]
                                  => unfold segment_prev_location end.
Hint Extern 1 => match goal with | [ |- context [segment_next_location]]
                                  => unfold segment_next_location end.

Section array_mapsto.

Definition array_mapsto' γ ns nc ℓ: iProp :=
  (∃ (dℓ: loc), ⌜ℓ = dℓ +ₗ Z.of_nat nc⌝ ∧ segment_data_location γ ns dℓ)%I.

Global Instance array_mapsto'_persistent γ ns nc ℓ:
  Persistent (array_mapsto' γ ns nc ℓ).
Proof. apply _. Qed.

Definition array_mapsto γ (id: nat) (ℓ: loc): iProp :=
  ias_cell_info_view (fun ns nc => array_mapsto' γ ns nc ℓ) id.

Theorem array_mapsto'_agree γ (ns nc: nat) (ℓ ℓ': loc):
  array_mapsto' γ ns nc ℓ -∗ array_mapsto' γ ns nc ℓ' -∗ ⌜ℓ = ℓ'⌝.
Proof.
  rewrite /array_mapsto'.
  iIntros "Ham Ham'".
  iDestruct "Ham" as (dℓ) "[% Ham]".
  iDestruct "Ham'" as (dℓ') "[% Ham']".
  iDestruct (segment_data_location_agree with "Ham Ham'") as %Hv.
  by subst.
Qed.

Theorem array_mapsto_agree γ n (ℓ ℓ': loc):
  array_mapsto γ n ℓ -∗ array_mapsto γ n ℓ' -∗ ⌜ℓ = ℓ'⌝.
Proof. apply array_mapsto'_agree. Qed.

Global Instance array_mapsto_persistent γ ns nc ℓ: Persistent (array_mapsto' γ ns nc ℓ).
Proof. apply _. Qed.

End array_mapsto.

Section cancellation.

Definition cell_is_cancelled' γ (ns nc: nat): iProp :=
  own γ (◯ (ias_cell_info' ns nc (Some (Cinl (to_agree tt))))).
Definition cell_is_cancelled γ := ias_cell_info_view (cell_is_cancelled' γ).

Global Instance cell_is_cancelled_timeless γ j:
  Timeless (cell_is_cancelled γ j).
Proof. apply _. Qed.

Global Instance cell_is_cancelled'_persistent γ ns nc:
  Persistent (cell_is_cancelled' γ ns nc).
Proof. apply _. Qed.

Definition cells_are_cancelled γ id (cells: vec bool (Pos.to_nat segment_size)) :=
  ([∗ list] i ↦ v ∈ vec_to_list cells,
   if (v: bool) then cell_is_cancelled' γ id i else True)%I.

Global Instance cells_are_cancelled_timeless γ id cells:
  Timeless (cells_are_cancelled γ id cells).
Proof. apply big_sepL_timeless. destruct x; apply _. Qed.

Definition segment_is_cancelled γ id :=
  cells_are_cancelled γ id (Vector.const true _).

Global Instance segment_is_cancelled_timeless γ j:
  Timeless (segment_is_cancelled γ j).
Proof. apply big_sepL_timeless. destruct x; apply _. Qed.

Global Instance cells_are_cancelled_persistent γ id cells:
  Persistent (cells_are_cancelled γ id cells).
Proof.
  rewrite /cells_are_cancelled. apply big_sepL_persistent.
  intros ? x. destruct x; apply _.
Qed.

Definition cell_cancellation_handle' γ (ns nc: nat): iProp :=
  own γ (◯ (ias_cell_info' ns nc (Some (Cinr (3/4)%Qp)))).

Theorem cell_cancellation_handle'_exclusive γ (ns nc: nat):
  cell_cancellation_handle' γ ns nc -∗ cell_cancellation_handle' γ ns nc -∗ False.
Proof.
  iIntros "HCh1 HCh2".
  iDestruct (own_valid_2 with "HCh1 HCh2") as %HContra.
  iPureIntro.
  revert HContra.
  rewrite auth_frag_valid -ias_cell_info'_op ias_cell_info'_valid.
  by case.
Qed.

Definition cell_cancellation_handle γ :=
  ias_cell_info_view (cell_cancellation_handle' γ).

End cancellation.

Definition is_valid_prev γ (id: nat) (pl: val): iProp :=
  (⌜pl = NONEV⌝ ∧
   ([∗ list] j ∈ seq 0 (id * Pos.to_nat segment_size),
    cell_is_cancelled γ j ∨ cell_is_done j) ∨
   ∃ (pid: nat) (prevℓ: loc),
     ⌜pid < id⌝ ∧ ⌜pl = SOMEV #prevℓ⌝ ∧
     segment_location γ pid prevℓ ∗
     [∗ list] j ∈ seq (S pid) (id - S pid), segment_is_cancelled γ j)%I.

Global Instance is_valid_prev_persistent γ id pl:
  Persistent (is_valid_prev γ id pl).
Proof. apply _. Qed.

Definition is_valid_next γ (id: nat) (nl: val): iProp :=
  (∃ (nid: nat) (nextℓ: loc),
      ⌜id < nid⌝ ∧ ⌜nl = SOMEV #nextℓ⌝ ∧
      segment_location γ nid nextℓ ∗
      [∗ list] j ∈ seq (S id) (nid - S id), segment_is_cancelled γ j)%I.

Global Instance is_valid_next_persistent γ id pl:
  Persistent (is_valid_prev γ id pl).
Proof. apply _. Qed.

Definition is_segment' γ (id cancelled: nat) (ℓ dℓ cℓ pℓ nℓ: loc)
           (pl nl: val): iProp :=
  (((pℓ ↦ pl ∗ nℓ ↦ nl)
      ∗ ℓ ↦ (((#id, #cℓ), #dℓ), (#pℓ, #nℓ))
      ∗ cℓ ↦ #cancelled)
     ∗ ([∗ list] i ∈ seq 0 (Pos.to_nat segment_size),
        cell_invariant γ (id*Pos.to_nat segment_size+i)%nat
                       (dℓ +ₗ Z.of_nat i))
     ∗ is_valid_prev γ id pl)%I.

Definition cell_cancellation_parts γ (id: nat)
           (cells: vec bool (Pos.to_nat segment_size)) :=
  ([∗ list] cid ↦ was_cancelled ∈ vec_to_list cells,
   if (was_cancelled: bool) then True
   else own γ (◯ (ias_cell_info' id cid (Some (Cinr (1/4)%Qp)))))%I.

Definition is_segment γ (id: nat) (ℓ: loc) (pl nl: val) : iProp :=
  (∃ dℓ cℓ pℓ nℓ cancelled,
      is_segment' γ id cancelled ℓ dℓ cℓ pℓ nℓ pl nl
                  ∗ segment_locations γ id (ℓ, (dℓ, cℓ), (pℓ, nℓ)) ∗
      (∃ (cells: vec bool (Pos.to_nat segment_size)),
          ⌜cancelled = length (List.filter (fun i => i) (vec_to_list cells))⌝ ∗
          cells_are_cancelled γ id cells ∗ cell_cancellation_parts γ id cells))%I.

Definition can_not_be_tail γ id := own γ (◯ (ias_segment_info (S id) ε)).

Definition is_normal_segment γ (ℓ: loc) (id: nat): iProp :=
  (∃ pl nl, is_segment γ id ℓ pl nl ∗ is_valid_next γ id nl)%I.

Definition is_tail_segment γ (ℓ: loc) (id: nat): iProp :=
  (∃ pl, is_segment γ id ℓ pl NONEV)%I.

Definition is_infinite_array γ : iProp :=
  (∃ segments, ([∗ list] i ↦ ℓ ∈ segments, is_normal_segment γ ℓ i)
                 ∗ (∃ ℓ, is_tail_segment γ ℓ (length segments))
                 ∗ (∃ segments', ⌜S (length segments) = length segments'⌝ ∧
                                 own γ (● segments')))%I.

Ltac iDestructHIsSeg :=
  iDestruct "HIsSeg" as (dℓ cℓ pℓ nℓ cancelled) "[HIsSeg [>#HLocs HCanc]]";
  iDestruct "HIsSeg" as "[[[Hpℓ Hnℓ] [Hℓ Hcℓ]] [#HCells #HValidPrev]]";
  iDestruct "HCanc" as (cancelled_cells) "[>-> [>#HCanc HCancParts]]".

Ltac iCloseHIsSeg := iMod ("HClose" with "[-]") as "HΦ";
  first by (rewrite /is_segment /is_segment'; eauto 20 with iFrame).

Theorem segment_id_spec γ id (ℓ: loc):
  <<< ∀ pl nl, ▷ is_segment γ id ℓ pl nl >>>
    segment_id #ℓ @ ⊤
  <<< is_segment γ id ℓ pl nl, RET #id >>>.
Proof.
  iIntros (Φ) "AU". wp_lam.
  wp_bind (!_)%E. iMod "AU" as (pl nl) "[HIsSeg [_ HClose]]".
  iDestructHIsSeg.
  wp_load.
  iCloseHIsSeg.
  iModIntro.
  by wp_pures.
Qed.

Theorem segment_prev_spec γ id (ℓ: loc):
  <<< ∀ pl nl, ▷ is_segment γ id ℓ pl nl >>>
    segment_prev #ℓ @ ⊤
    <<< ∃ (pℓ: loc),
          is_segment γ id ℓ pl nl ∗ segment_prev_location γ id pℓ, RET #pℓ >>>.
Proof.
  iIntros (Φ) "AU". wp_lam.
  wp_bind (!_)%E. iMod "AU" as (pl nl) "[HIsSeg [_ HClose]]".
  iDestructHIsSeg.
  wp_load.
  iCloseHIsSeg.
  by iModIntro; wp_pures; auto.
Qed.

Theorem segment_prev_read_spec γ id (ℓ pℓ: loc):
  segment_prev_location γ id pℓ -∗
  <<< ∀ pl nl, ▷ is_segment γ id ℓ pl nl >>>
    ! #pℓ @ ⊤
  <<< is_segment γ id ℓ pl nl ∗ is_valid_prev γ id pl, RET pl >>>.
Proof.
  iIntros "#HIsPrevLoc". iIntros (Φ) "AU".
  iMod "AU" as (pl nl) "[HIsSeg [_ HClose]]".
  rename pℓ into pℓ'. iDestructHIsSeg.
  iAssert (segment_prev_location γ id pℓ) as "#HPrevLoc"; first by eauto 6.
  iDestruct (segment_prev_location_agree with "HIsPrevLoc HPrevLoc") as %->.
  wp_load.
  iCloseHIsSeg.
  iModIntro.
  by wp_pures.
Qed.

Theorem segment_prev_write_spec γ id (ℓ pℓ: loc) (pl: val):
  segment_prev_location γ id pℓ -∗ is_valid_prev γ id pl -∗
  <<< ∀ pl' nl, ▷ is_segment γ id ℓ pl' nl >>>
  #pℓ <- pl @ ⊤
  <<< is_segment γ id ℓ pl nl, RET #() >>>.
Proof.
  iIntros "#HIsPrevLoc #HIsValidPrev". iIntros (Φ) "AU".
  iMod "AU" as (pl' nl) "[HIsSeg [_ HClose]]".
  rename pℓ into pℓ'. iDestructHIsSeg.
  iAssert (segment_prev_location γ id pℓ) as "#HPrevLoc"; first by eauto 6.
  iDestruct (segment_prev_location_agree with "HIsPrevLoc HPrevLoc") as %->.
  wp_store.
  iCloseHIsSeg.
  by iModIntro.
Qed.

Theorem segment_next_spec γ id (ℓ: loc):
  <<< ∀ pl nl, ▷ is_segment γ id ℓ pl nl >>>
    segment_next #ℓ @ ⊤
  <<< ∃ (nℓ: loc),
        is_segment γ id ℓ pl nl ∗ segment_next_location γ id nℓ, RET #nℓ >>>.
Proof.
  iIntros (Φ) "AU". wp_lam.
  wp_bind (!_)%E. iMod "AU" as (pl nl) "[HIsSeg [_ HClose]]".
  iDestructHIsSeg.
  wp_load.
  iCloseHIsSeg.
  iModIntro.
  by wp_pures.
Qed.

Theorem segment_next_read_spec γ id (ℓ nℓ: loc):
  segment_next_location γ id nℓ -∗
  <<< ∀ pl nl, ▷ is_segment γ id ℓ pl nl >>>
    ! #nℓ @ ⊤
  <<< is_segment γ id ℓ pl nl, RET nl >>>.
Proof.
  iIntros "#HIsNextLoc".
  iIntros (Φ) "AU". iMod "AU" as (pl nl) "[HIsSeg [_ HClose]]".
  rename nℓ into nℓ'. iDestructHIsSeg.
  iAssert (segment_next_location γ id nℓ) as "#HNextLoc"; first by eauto 6.
  iDestruct (segment_next_location_agree with "HIsNextLoc HNextLoc") as %->.
  wp_load.
  iCloseHIsSeg.
  iModIntro.
  by wp_pures.
Qed.

Theorem segment_next_write_spec γ id (ℓ nℓ: loc) (nl: val):
  segment_next_location γ id nℓ -∗
  <<< ∀ pl nl', ▷ is_segment γ id ℓ pl nl' >>>
    #nℓ <- nl @ ⊤
  <<< is_segment γ id ℓ pl nl, RET #() >>>.
Proof.
  iIntros "#HIsNextLoc".
  iIntros (Φ) "AU". iMod "AU" as (pl nl') "[HIsSeg [_ HClose]]".
  rename nℓ into nℓ'. iDestructHIsSeg.
  iAssert (segment_next_location γ id nℓ) as "#HNextLoc"; first by eauto 6.
  iDestruct (segment_next_location_agree with "HIsNextLoc HNextLoc") as %->.
  wp_store.
  iCloseHIsSeg.
  by iModIntro.
Qed.

Theorem segment_canc_spec γ id (ℓ: loc):
  <<< ∀ pl nl, ▷ is_segment γ id ℓ pl nl >>>
    segment_cancelled #ℓ @ ⊤
    <<< ∃ (cℓ: loc),
          is_segment γ id ℓ pl nl ∗ segment_canc_location γ id cℓ, RET #cℓ >>>.
Proof.
  iIntros (Φ) "AU". wp_lam.
  wp_bind (!_)%E. iMod "AU" as (pl nl) "[HIsSeg [_ HClose]]".
  iDestructHIsSeg.
  wp_load.
  iCloseHIsSeg.
  iModIntro.
  by wp_pures.
Qed.

Theorem segment_canc_read_spec γ id (ℓ cℓ: loc):
  segment_canc_location γ id cℓ -∗
  <<< ∀ pl nl, ▷ is_segment γ id ℓ pl nl >>>
    ! #cℓ @ ⊤
  <<< ∃ (cancelled: nat), is_segment γ id ℓ pl nl ∗
      (∃ cells,
          cells_are_cancelled γ id cells
          ∗ ⌜cancelled = length (List.filter (fun i => i) (vec_to_list cells))⌝),
      RET #cancelled >>>.
Proof.
  iIntros "#HIsCancLoc".
  iIntros (Φ) "AU". iMod "AU" as (pl nl) "[HIsSeg [_ HClose]]".
  rename cℓ into cℓ'. iDestructHIsSeg.
  iAssert (segment_canc_location γ id cℓ) as "#HCancLoc"; first by eauto 6.
  iDestruct (segment_canc_location_agree with "HIsCancLoc HCancLoc") as %->.
  wp_load.
  iCloseHIsSeg.
  iModIntro.
  by wp_pures.
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

Lemma big_sepL_list_alter {A: Type} {P: nat -> A -> iProp} (f: A -> A) v i x':
  ⌜v !! i = Some x'⌝ -∗
  ([∗ list] k ↦ x ∈ v, P k x) -∗
  (P i (f x')) -∗
  (P i x' ∗ [∗ list] k ↦ x ∈ alter f i v, P k x).
Proof.
  iIntros "% HList HVal".
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

Lemma segment_info_to_cell_info' l γ id:
  forall k, own γ (◯ ias_segment_info id (ε, replicate k ε ++ l)) ≡
  (([∗ list] i ↦ e ∈ l, own γ (◯ ias_cell_info' id (k+i)%nat e)) ∗
  own γ (◯ ias_segment_info id (ε, replicate (k + length l)%nat ε)))%I.
Proof.
  induction l; simpl; intros.
  { by rewrite -plus_n_O app_nil_r bi.emp_sep. }
  rewrite -plus_n_O -plus_n_Sm.
  assert (
      own γ (◯ ias_segment_info id (ε, replicate k ε ++ a :: l)) ≡
      (own γ (◯ ias_segment_info id (ε, replicate (S k) ε ++ l)) ∗
       own γ (◯ ias_cell_info' id k a))%I) as ->.
  {
    rewrite -own_op /ias_cell_info' -auth_frag_op -ias_segment_info_op -pair_op.
    rewrite ucmra_unit_left_id.
    assert (((replicate (S k) ε ++ l) ⋅ (replicate k ε ++ [a])) ≡
            replicate k ε ++ a :: l) as ->.
    { apply list_equiv_lookup.
      induction k; case; simpl; try done.
      by rewrite ucmra_unit_left_id.
      intros n. rewrite list_lookup_op.
      by destruct (l !! n). }
    done.
  }
  rewrite IHl.
  rewrite bi.sep_comm bi.sep_assoc.
  assert (([∗ list] i ↦ e ∈ l, own γ (◯ ias_cell_info' id (S k + i)%nat e))%I ≡
          ([∗ list] i ↦ e ∈ l, own γ (◯ ias_cell_info' id (k + S i)%nat e))%I) as ->.
  2: done.
  apply big_sepL_proper.
  intros.
  by rewrite -plus_n_Sm.
Qed.

Theorem segment_canc_incr_spec γ id cid (ℓ cℓ: loc) segments:
  (cid < Pos.to_nat segment_size)%nat ->
  segment_canc_location γ id cℓ -∗
  <<< ∀ pl nl, ▷ is_segment γ id ℓ pl nl ∗
                              cell_cancellation_handle' γ id cid ∗
                              own γ (● segments) >>>
    FAA #cℓ #1 @ ⊤
  <<< ∃ (cancelled: nat),
        is_segment γ id ℓ pl nl ∗
    (∃ cells,
          cells_are_cancelled γ id cells
          ∗ ⌜S cancelled = length (List.filter (fun i => i) (vec_to_list cells))⌝) ∗
    (∃ segments', own γ (● segments')),
    RET #cancelled >>>.
Proof.
  iIntros (HCid) "#HIsCancLoc". iIntros (Φ) "AU".
  iMod "AU" as (pl nl) "[[HIsSeg [HCancHandle HAuth]] [_ HClose]]".
  rename cℓ into cℓ'. iDestructHIsSeg.
  iAssert (segment_canc_location γ id cℓ) as "#HCancLoc"; first by eauto 6.
  iDestruct (segment_canc_location_agree with "HIsCancLoc HCancLoc") as %->.
  rewrite /cell_cancellation_handle'.
  destruct (list_lookup cid cancelled_cells) as [[|]|] eqn:HWasNotCancelled.
  3: {
    apply lookup_ge_None in HWasNotCancelled.
    rewrite vec_to_list_length in HWasNotCancelled.
    exfalso; lia.
  }
  1: {
    rewrite /cells_are_cancelled.
    iAssert (▷ cell_is_cancelled' γ id cid)%I as ">HCidCanc". {
      iApply bi.later_mono. iIntros "HCanc".
      2: by iApply "HCanc".
      iDestruct big_sepL_lookup as "HH".
      2: done.
      2: iSpecialize ("HH" with "HCanc").
      apply _. done.
    }
    rewrite /cell_is_cancelled'.
    iDestruct (own_valid_2 with "HCancHandle HCidCanc") as %HContra.
    exfalso. move: HContra. rewrite -auth_frag_op -ias_cell_info'_op -Some_op.
    rewrite auth_frag_valid ias_cell_info'_valid. by case.
  }
  remember (VectorDef.replace_order cancelled_cells HCid true) as cancelled_cells'.
  iAssert (▷ (own γ (◯ ias_cell_info' id cid (Some (Cinr (1 / 4)%Qp)))
          ∗ cell_cancellation_parts γ id cancelled_cells'))%I
          with "[HCancParts]" as "[>HCancMain HCancParts']".
  { rewrite /cell_cancellation_parts.
    subst.
    rewrite VectorDef_replace_order_list_alter.
    iDestruct (big_sepL_list_alter with "[]") as "HOwnFr".
    { iPureIntro. unfold lookup. apply HWasNotCancelled. }
    iSpecialize ("HOwnFr" with "HCancParts").
    by iApply "HOwnFr".
  }
  iCombine "HCancMain" "HCancHandle" as "HCancPermit".
  rewrite -ias_cell_info'_op -Some_op -Cinr_op.
  replace ((1/4) ⋅ (3/4))%Qp with 1%Qp
    by (symmetry; apply Qp_quarter_three_quarter).
  iMod (own_update_2 with "HAuth HCancPermit") as "[HAuth HSeg]".
  { apply auth_update.
    apply (let update_list := list_alter (fun _ => Some (Cinl (to_agree ()))) cid in
           let auth_fn x := (x.1, update_list x.2) in
           let frag_fn x := (x.1, update_list x.2)
           in list_alter_local_update id auth_fn frag_fn).
    rewrite ias_segment_info_lookup.
    simpl.
    unfold lookup.
    destruct (list_lookup id segments); simpl.
    2: by apply None_local_update.
    apply option_local_update.
    apply prod_local_update_2; simpl.
    apply list_alter_local_update.
    rewrite lookup_app_r replicate_length. 2: lia.
    rewrite -minus_diag_reverse; simpl.
    remember (_ !! _) as K.
    destruct K as [u'|].
    2: by apply None_local_update.
    apply option_local_update.
    apply transitivity with (y := (None, None)).
    - apply delete_option_local_update.
      apply Cinr_exclusive.
      by apply frac_full_exclusive.
    - apply alloc_option_local_update.
      done.
  }
  rewrite ias_segment_info_alter.
  simpl.
  replace (list_alter _ cid _) with (replicate cid ε ++ [Some (Cinl (to_agree ()))]).
  2: {
    apply list_eq; intros.
    clear.
    generalize dependent i.
    induction cid; destruct i; simpl; auto.
  }
  iAssert (cell_is_cancelled' γ id cid) with "HSeg" as "#HSeg'".
  iClear "HSeg".
  iAssert (cells_are_cancelled γ id cancelled_cells')%I as "HCancLoc'".
  { rewrite /cells_are_cancelled.
    subst. rewrite VectorDef_replace_order_list_alter.
    iDestruct (big_sepL_list_alter (fun _ => true) with "[]") as "HOwnFr".
    { iPureIntro. apply HWasNotCancelled. }
    iSpecialize ("HOwnFr" with "HCanc HSeg'").
    iDestruct "HOwnFr" as "[_ HOwnFr]". done.
  }
  iRevert "HCancLoc'".
  iIntros "#HCancLoc'".
  wp_faa.
  assert (length (List.filter (fun i => i) cancelled_cells) + 1 =
          Z.of_nat (length (List.filter (fun i => i) cancelled_cells'))) as Hlen.
  { subst. rewrite VectorDef_replace_order_list_alter.
    remember (vec_to_list cancelled_cells) as K.
    rewrite Z.add_comm. replace 1 with (Z.of_nat (S O)) by auto.
    rewrite -Nat2Z.inj_add. simpl. apply inj_eq.
    move: HWasNotCancelled. clear.
    generalize dependent cid.
    unfold alter.
    induction K; simpl.
    - discriminate.
    - destruct cid.
      { intros [= ->]. simpl. lia. }
      { intros. destruct a; simpl; auto. }
  }
  rewrite Hlen.
  iMod ("HClose" $! (length (List.filter (fun i => i) (vec_to_list cancelled_cells)))%nat
          with "[-]") as "HΦ".
  2: by iModIntro.
  iSplitR "HAuth".
  {
    rewrite /is_segment /is_segment'.
    eauto 20 with iFrame.
  }
  {
    iSplitR.
    2: by eauto with iFrame.
    iExists _.
    iSplitL.
    iApply "HCancLoc'".
    iPureIntro.
    lia.
  }
Qed.

Theorem segment_data_at_spec γ id (ℓ: loc) (ix: nat):
  ⌜ix < Pos.to_nat segment_size⌝ -∗
  <<< ∀ pl nl, ▷ is_segment γ id ℓ pl nl >>>
    segment_data_at #ℓ #ix @ ⊤
  <<< ∃ (v: loc), is_segment γ id ℓ pl nl
                             ∗ array_mapsto' γ id ix v
                             ∗ cell_invariant γ
                             (id * Pos.to_nat segment_size + ix)%nat v,
  RET #v >>>.
Proof.
  iIntros "%". iIntros (Φ) "AU". wp_lam. wp_pures.
  wp_bind (!_)%E. iMod "AU" as (pl nl) "[HIsSeg [_ HClose]]".
  iDestructHIsSeg.
  wp_load.
  iSpecialize ("HClose" $! (dℓ +ₗ ix)).
  iMod ("HClose" with "[-]") as "HΦ".
  { rewrite /is_segment /is_segment'.
    iAssert (cell_invariant γ (id * Pos.to_nat segment_size + ix)%nat
                            (dℓ +ₗ ix)) as "#HCellInv".
    { iApply (big_sepL_elem_of with "HCells").
      apply elem_of_list_In. apply in_seq. lia. }
    rewrite /array_mapsto'.
    by eauto 30 with iFrame.
  }
  iModIntro.
  by wp_pures.
Qed.

Theorem new_segment_spec γ (id: nat) pl :
  {{{ is_valid_prev γ id pl }}}
    (new_segment segment_size) #id pl
  {{{ (ℓ dℓ cℓ pℓ nℓ: loc), RET #ℓ;
      ([∗ list] i ∈ seq O (Pos.to_nat segment_size),
       ((dℓ +ₗ Z.of_nat i) ↦ InjLV #())
         -∗ cell_invariant γ (id * Pos.to_nat segment_size + i)%nat (dℓ +ₗ i)) -∗
      is_segment' γ id O ℓ dℓ cℓ pℓ nℓ pl NONEV }}}.
Proof.
  iIntros (Φ) "#HValidPrev HPost". wp_lam. wp_pures.
  wp_bind ((_, _))%E.
  wp_bind (ref _)%E. wp_alloc nℓ as "Hnℓ".
  wp_bind (ref _)%E. wp_alloc pℓ as "Hpℓ".
  wp_pures.
  wp_bind (AllocN _ _)%E. wp_alloc dℓ as "Hdℓ"; first done.
  wp_bind (ref _)%E. wp_alloc cℓ as "Hcℓ".
  wp_pures.
  wp_alloc ℓ as "Hℓ".
  iApply "HPost".
  rewrite /is_segment'.
  iIntros "HCInv".
  iSplitL "Hpℓ Hnℓ Hℓ Hcℓ".
  { iSplitR "Hℓ Hcℓ"; iFrame. }
  iSplitL. 2: done.
  rewrite /array.
  replace (Z.to_nat (Z.pos segment_size)) with (Pos.to_nat segment_size) by auto.
  remember (id * Pos.to_nat segment_size)%nat as k. clear Heqk.
  assert ((fun (i: nat) v => (dℓ +ₗ i) ↦ v) = fun (i: nat) v => (dℓ +ₗ (O + i)) ↦ v)%I as -> by auto.
  remember O as z. clear Heqz.
  remember (Pos.to_nat segment_size) as y. clear Heqy.
  iInduction (y) as [|y'] "IH" forall (z). all: simpl; auto.
  iDestruct "HCInv" as "[HCCur HCInv]". iDestruct "Hdℓ" as "[HdℓCur Hdℓ]".
  rewrite Z.add_0_r.
  iSpecialize ("HCCur" with "HdℓCur").
  iFrame.
  iApply ("IH" $! (S z) with "[Hdℓ]"); auto.
  iApply big_sepL_mono. 2: done.
  simpl. intros k' ? ?. replace (z + S k') with (S z + k') by lia.
  done.
Qed.

Lemma segment_by_location γ id ℓ:
  segment_location γ id ℓ -∗ is_infinite_array γ -∗
  ((is_normal_segment γ ℓ id ∗ (is_normal_segment γ ℓ id -∗ is_infinite_array γ)) ∨
   (is_tail_segment γ ℓ id ∗ (is_tail_segment γ ℓ id -∗ is_infinite_array γ))).
Proof.
  iIntros "#HSegLoc HInfArr".
  iDestruct "HInfArr" as (segments) "[HNormSegs [HTailSeg HAuth]]".
  iDestruct "HAuth" as (segments') "[% HAuth]".
  destruct (le_lt_dec (length segments) id).
  { inversion l; subst.
    2: {
      rewrite /segment_location /segment_locations.
      iDestruct "HSegLoc" as (? ? ? ?) "#HSeg".
      iDestruct (own_valid_2 with "HAuth HSeg")
        as %[HValid _]%auth_both_valid.
      exfalso. revert HValid. rewrite list_lookup_included.
      intro HValid. specialize (HValid (S m)).
      rewrite ias_segment_info_lookup in HValid.
      assert (length segments' <= S m)%nat as HIsNil by lia.
      apply lookup_ge_None in HIsNil. rewrite HIsNil in HValid.
      apply option_included in HValid.
      destruct HValid as [[=]|[a [b [_ [[=] _]]]]].
    }
    iDestruct "HTailSeg" as (ℓ' pl) "HIsSeg".
    destruct (decide (ℓ = ℓ')); subst.
    2: {
      iDestruct "HIsSeg" as (? ? ? ? ?) "[_ [HLocs _]]".
      iAssert (segment_location γ (length segments) ℓ') as "#HLoc";
        first by eauto 6.
      iDestruct (segment_location_agree with "HSegLoc HLoc") as %->.
      contradiction.
    }
    iRight.
    iSplitL "HIsSeg"; first by rewrite /is_tail_segment; eauto with iFrame.
    iIntros "HTailSeg". rewrite /is_infinite_array.
    iExists segments. iFrame. iSplitR "HAuth"; eauto 10 with iFrame.
  }
  apply lookup_lt_is_Some_2 in l. destruct l as [x Hx].
  iDestruct (big_sepL_lookup_acc with "[HNormSegs]") as "[HIsSeg HRestSegs]".
  2: by iApply "HNormSegs".
  apply Hx.
  simpl.
  iLeft.
  destruct (decide (ℓ = x)); subst.
  2: {
    iDestruct "HIsSeg" as (pl nl) "[HIsSeg #HValNext]".
    iDestruct "HIsSeg" as (? ? ? ? ?) "[_ [HLocs _]]".
    iAssert (segment_location γ id x) as "#HLoc";
      first by eauto 6.
    iDestruct (segment_location_agree with "HSegLoc HLoc") as %->.
    contradiction.
  }
  iFrame.
  iIntros "HNormSeg". rewrite /is_infinite_array.
  iExists segments. iFrame. iSplitR "HAuth".
  { by iApply "HRestSegs". }
  eauto 10 with iFrame.
Qed.

Lemma is_segment_by_location_prev γ id ℓ:
  segment_location γ id ℓ -∗ is_infinite_array γ -∗
  ∃ nl, (∃ pl, is_segment γ id ℓ pl nl) ∗
                      (∀ pl, is_segment γ id ℓ pl nl -∗ is_infinite_array γ).
Proof.
  iIntros "#HSegLoc HInfArr".
  iDestruct (segment_by_location with "HSegLoc HInfArr")
    as "[[HNorm HRest]|[HTail HRest]]".
  1: iDestruct "HNorm" as (pl nl) "[HIsSeg #HValNext]".
  2: iDestruct "HTail" as (pl) "HIsSeg".
  all: iExists _; iSplitL "HIsSeg"; try by eauto 10.
  all: iIntros (?) "HSeg"; iApply "HRest".
  { rewrite /is_normal_segment. eauto 10 with iFrame. }
  { rewrite /is_tail_segment. eauto 10 with iFrame. }
Qed.

Lemma is_segment_by_location γ id ℓ:
  segment_location γ id ℓ -∗ is_infinite_array γ -∗
  ∃ pl nl, is_segment γ id ℓ pl nl ∗
                      (is_segment γ id ℓ pl nl -∗ is_infinite_array γ).
Proof.
  iIntros "#HSegLoc HInfArr".
  iDestruct (is_segment_by_location_prev with "HSegLoc HInfArr")
    as (nl) "[HIsSeg HArrRestore]".
  iDestruct "HIsSeg" as (pl) "HIsSeg".
  iExists _, _; iFrame. iApply "HArrRestore".
Qed.

Definition cell_init : iProp :=
  (□ (∀ γ id ℓ, cell_cancellation_handle γ id -∗ ℓ ↦ NONEV -∗
                                         |==> cell_invariant γ id ℓ))%I.

Definition is_segment_queue_inv γ tl : iProp :=
  (is_infinite_array γ ∗ ∃ id ℓ,
        ([∗ list] j ∈ seq 0 (id * Pos.to_nat segment_size),
         cell_is_processed j) ∗
        segment_location γ id ℓ ∗ tl ↦ #ℓ)%I.

Definition is_segment_queue γ v: iProp :=
  (∃ (tl: loc), cell_init ∗ ⌜v = #tl⌝ ∗ inv N (is_segment_queue_inv γ tl))%I.

Theorem is_segment_queue_persistent γ v: Persistent (is_segment_queue γ v).
Proof. apply _. Qed.

Lemma local_update_refl {A: cmraT}: forall (a b: A),
  (a, b) ~l~> (a, b).
Proof.
  intros. unfold local_update. intros. simpl in *. split; done.
Qed.


Theorem move_tail_forward_spec γ v id ℓ:
  {{{ is_segment_queue γ v ∗ segment_location γ id ℓ ∗
      [∗ list] j ∈ seq 0 (id * Pos.to_nat segment_size), cell_is_processed j
  }}}
    move_tail_forward v #ℓ
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "[#HIsSegQ [#HSegLoc #HProc]] HPost". rewrite /is_segment_queue.
  iDestruct "HIsSegQ" as (tl) "[_ [% HSeqInv]]"; subst. wp_lam.
  rewrite /array_tail. wp_pures.
  iLöb as "IH".
  wp_bind (!_)%E.
  iInv N as "[HIsInf Htl]" "HClose".
  iDestruct "Htl" as (id' ℓ') "[HProcOld [#HLoc Htl]]".
  wp_load.
  iMod ("HClose" with "[HIsInf HProcOld Htl HLoc]") as "_".
  { rewrite /is_segment_queue_inv. eauto 10 with iFrame. }
  iModIntro. wp_pures.
  wp_bind (segment_id #ℓ').
  awp_apply segment_id_spec without "HPost". iInv N as "[HIsInf Htl]".
  iDestruct (is_segment_by_location with "HLoc HIsInf")
    as (? ?) "[HIsSeg HArrRestore]".
  iAaccIntro with "HIsSeg"; iFrame; iIntros "HIsSeg"; iModIntro.
  1: by iApply "HArrRestore".
  iSplitL. by iApply "HArrRestore".
  iIntros "HPost".
  awp_apply segment_id_spec without "HPost". iInv N as "[HIsInf Htl]".
  iDestruct (is_segment_by_location with "HSegLoc HIsInf")
    as (? ?) "[HIsSeg HArrRestore]".
  iAaccIntro with "HIsSeg"; iFrame "Htl"; iIntros "HIsSeg"; iModIntro.
  1: by iApply "HArrRestore".
  iSplitL. by iApply "HArrRestore".
  iIntros "HPost".
  wp_pures.
  destruct (bool_decide (id <= id')); wp_pures.
  1: by iApply "HPost".
  wp_bind (CmpXchg _ _ _).
  iInv N as "[HIsInf Htl]" "HClose".
  iDestruct "Htl" as (id'' ℓ'') "[#HProc' [#HLocs Htl]]".
  destruct (decide (ℓ'' = ℓ')); subst.
  {
    wp_cmpxchg_suc.
    iMod ("HClose" with "[HIsInf Htl]") as "_".
    { iFrame. iExists id. iExists ℓ. eauto 10 with iFrame. }
    iModIntro. wp_pures. by iApply "HPost".
  }
  {
    wp_cmpxchg_fail.
    iMod ("HClose" with "[HIsInf Htl]") as "_".
    { iFrame. iExists id''. iExists ℓ''. eauto 10 with iFrame. }
    iModIntro. wp_pures. wp_lam. wp_pures.
    rewrite /array_tail. wp_pures.
    iApply ("IH" with "HPost").
  }
Qed.

Theorem move_head_forward_spec γ id (ℓ: loc):
  ([∗ list] j ∈ seq 0 (id * Pos.to_nat segment_size),
    (cell_is_cancelled γ j ∨ cell_is_done j))%I -∗
  <<< ∀ pl nl, ▷ is_segment γ id ℓ pl nl >>>
    segment_cutoff #ℓ @ ⊤
  <<< is_segment γ id ℓ (InjLV #()) nl, RET #() >>>.
Proof.
  iIntros "#HDone". iIntros (Φ) "AU". wp_lam.
  rewrite /segment_prev. wp_pures.
  wp_bind (! #ℓ)%E.
  iMod "AU" as (pl nl) "[HIsSeg [HClose _]]".
  iDestructHIsSeg. wp_load. iCloseHIsSeg.
  iModIntro. wp_pures.
  iMod "HΦ" as (pl' nl') "[HIsSeg [_ HClose]]".
  iDestruct "HIsSeg" as (dℓ' cℓ' pℓ' nℓ' cancelled_cells')
                          "[HIsSeg [>#HLocs' HCanc']]".
  iDestruct "HIsSeg" as "[[[HH HH'''] HH''] [HH' HHVP]]".
  iDestruct (segment_locations_agree with "HLocs HLocs'") as %HH.
  revert HH. intros [=]. subst. wp_store.
  iMod ("HClose" with "[-]") as "HPost".
  { rewrite /is_segment /is_segment' /is_valid_prev.
    eauto 20 with iFrame. }
  done.
Qed.

Lemma normal_segment_by_location γ id ℓ:
  segment_location γ id ℓ -∗ can_not_be_tail γ id -∗ is_infinite_array γ -∗
  (is_normal_segment γ ℓ id ∗ (is_normal_segment γ ℓ id -∗ is_infinite_array γ)).
Proof.
  iIntros "#HSegLoc #HNotTail HInfArr".
  iDestruct "HInfArr" as (segments) "[HNormSegs [HTail HAuth]]".
  iDestruct "HAuth" as (segments') "[% HAuth]".
  destruct (le_lt_dec (length segments) id).
  {
    iDestruct (own_valid_2 with "HAuth HNotTail") as %HContra.
    exfalso. move: HContra.
    rewrite auth_both_valid; case. rewrite list_lookup_included.
    intros HContra _. specialize (HContra (S id)). revert HContra.
    rewrite ias_segment_info_lookup.
    assert (length segments' <= S id)%nat as HIsNil by lia.
    apply lookup_ge_None in HIsNil. rewrite HIsNil.
    rewrite option_included. intros HValid.
    destruct HValid as [[=]|[a [b [_ [[=] _]]]]].
  }
  apply lookup_lt_is_Some_2 in l. destruct l as [x Hx].
  iDestruct (big_sepL_lookup_acc with "[HNormSegs]") as "[HIsSeg HRestSegs]".
  by apply Hx. done. simpl. destruct (decide (ℓ = x)); subst.
  2: {
    iDestruct "HIsSeg" as (pl nl) "[HIsSeg #HValNext]".
    iDestruct "HIsSeg" as (? ? ? ? ?) "[_ [HLocs _]]".
    iAssert (segment_location γ id x) as "#HLoc";
      first by eauto 6.
    iDestruct (segment_location_agree with "HSegLoc HLoc") as %->.
    contradiction.
  }
  iFrame.
  iIntros "HNormSeg". rewrite /is_infinite_array.
  iSpecialize ("HRestSegs" with "HNormSeg").
  eauto 10 with iFrame.
Qed.

Theorem can_not_be_tail_if_has_next γ id nl:
  is_valid_next γ id nl -∗ can_not_be_tail γ id.
Proof.
  iIntros "HValidNext".
  iDestruct "HValidNext" as (nid nℓ) "(% & -> & #SegLoc & _)".
  assert (id < nid)%nat as HLt by lia.
  revert HLt. clear. intros ?.
  iDestruct "SegLoc" as (? ? ? ?) "SegLoc".
  rewrite /segment_locations. remember (_, _) as K.
  rewrite /can_not_be_tail.
  clear HeqK.
  iAssert (ias_segment_info nid K ≡ ias_segment_info nid K ⋅
                            ias_segment_info (S id) ε)%I as "HH".
  { iClear "SegLoc". rewrite /ias_segment_info.
    iPureIntro. apply list_equiv_lookup. intros i.
    simpl. rewrite list_lookup_op. generalize dependent i.
    generalize dependent id.
    induction nid as [|nid']; intros; first by lia.
    simpl. destruct i; first done; simpl.
    destruct id; simpl. 2: by apply IHnid'; lia.
    destruct nid'; simpl; destruct i; simpl; try done.
    - by rewrite -Some_op ucmra_unit_right_id.
    - by destruct ((replicate nid' _ ++ _) !! _).
  }
  iRewrite "HH" in "SegLoc".
  rewrite auth_frag_op own_op.
  iDestruct "SegLoc" as "[_ $]".
Qed.

Theorem segment_move_next_to_right_spec γ id (ℓ: loc) mnl:
  segment_location γ id ℓ -∗
  is_valid_next γ id mnl -∗
  <<< ▷ is_infinite_array γ >>>
    segment_move_next_to_right #ℓ mnl @ ⊤
  <<< ▷ is_infinite_array γ, RET #() >>>.
Proof.
  iIntros "#HSegLoc #HValidNewNext". iIntros (Φ) "AU". wp_lam.
  rewrite /from_some. wp_pures.
  iDestruct (can_not_be_tail_if_has_next with "HValidNewNext") as "#HNotTail".
  iLöb as "IH".

  awp_apply segment_next_spec. iApply (aacc_aupd_abort with "AU"); first done.
  iIntros "HInfArr".
  iDestruct (normal_segment_by_location with "HSegLoc HNotTail HInfArr")
    as "[HNormSeg HArrRestore]".
  iDestruct "HNormSeg" as (? ?) "(HIsSeg & #HValidNext)".
  iAaccIntro with "HIsSeg".
  { iIntros "HIsSeg !>". iSplitL. 2: by eauto. iApply "HArrRestore".
    rewrite /is_normal_segment. iExists _, _.
    iFrame "HIsSeg HValidNext HNotTail". }
  iIntros (nℓ) "[HIsSeg #HNextLoc] !>".
  iSplitL.
  { rewrite /is_normal_segment. iApply "HArrRestore".
    iExists _, _. iFrame "HIsSeg HValidNext HNotTail". }
  iClear "HValidNext".
  iIntros "AU !>".

  awp_apply segment_next_read_spec; first done.
  iApply (aacc_aupd_abort with "AU"); first done.
  iIntros "HInfArr".
  iDestruct (normal_segment_by_location with "HSegLoc HNotTail HInfArr")
    as "[HNormSeg HArrRestore]".
  iDestruct "HNormSeg" as (? ?) "(HIsSeg & #HValidNext)".
  iAaccIntro with "HIsSeg".
  { iIntros "HIsSeg !>". iSplitL. 2: by eauto.
    iApply "HArrRestore". rewrite /is_normal_segment. iExists _, _.
    iFrame "HIsSeg HValidNext HNotTail". }
  iIntros "HIsSeg !>". iSplitL.
  { iApply "HArrRestore". rewrite /is_normal_segment. iExists _, _.
    iFrame "HIsSeg HValidNext HNotTail". }
  iIntros "AU !>".
  iDestruct "HValidNext" as (nid nextℓ) "(_ & >-> & >#HNextSegLoc & _)".

  wp_pures.

  awp_apply segment_id_spec. iApply (aacc_aupd_abort with "AU"); first done.
  iIntros "HInfArr".
  iDestruct (is_segment_by_location with "HNextSegLoc HInfArr")
    as (? ?) "[HIsSeg HArrRestore]".
  iAaccIntro with "HIsSeg"; iIntros "HIsSeg !>".
  { iSplitL; by [iApply "HArrRestore"|eauto]. }
  iSplitL; first by iApply "HArrRestore". iIntros "AU !>".

  iDestruct "HValidNewNext" as (nnid ?) "(% & -> & #HNewNextSegLoc & HNewCanc)".
  wp_pures.

  awp_apply segment_id_spec. iApply (aacc_aupd_abort with "AU"); first done.
  iIntros "HInfArr".
  iDestruct (is_segment_by_location with "HNewNextSegLoc HInfArr")
    as (? ?) "[HIsSeg HArrRestore]".
  iAaccIntro with "HIsSeg"; iIntros "HIsSeg !>".
  { iSplitL; by [iApply "HArrRestore"|eauto]. }
  iSplitL; first by iApply "HArrRestore". iIntros "AU".

  destruct (bool_decide (nnid <= nid)) eqn:E.
  iMod "AU" as "[HInfArr [_ HClose]]"; iMod ("HClose" with "HInfArr") as "HΦ".
  all: iModIntro; wp_pures; rewrite E; wp_pures.
  1: done.

  awp_apply segment_next_spec. iApply (aacc_aupd_abort with "AU"); first done.
  iIntros "HInfArr".
  iDestruct (normal_segment_by_location with "HSegLoc HNotTail HInfArr")
    as "[HNormSeg HArrRestore]".
  iDestruct "HNormSeg" as (? ?) "(HIsSeg & #HValidNext)".
  iAaccIntro with "HIsSeg".
  { iIntros "HIsSeg !>". iSplitL. 2: by eauto. iApply "HArrRestore".
    rewrite /is_normal_segment. iExists _, _.
    iFrame "HIsSeg HValidNext HNotTail". }
  iIntros (?) "[HIsSeg #HNextLoc'] !>".
  iSplitL.
  { rewrite /is_normal_segment. iApply "HArrRestore".
    iExists _, _. iFrame "HIsSeg HValidNext HNotTail". }
  iClear "HValidNext".
  iIntros "AU !>".

  iDestruct (segment_next_location_agree with "HNextLoc' HNextLoc") as %->.
  iClear "HNextLoc'".
  wp_bind (CmpXchg _ _ _). iMod "AU" as "[HInfArr HClose]".
  iDestruct (normal_segment_by_location with "HSegLoc HNotTail HInfArr")
    as "[HIsNormSeg HArrRestore]".
  iDestruct "HIsNormSeg" as (pl nl) "(HIsSeg & #HValidNext)".
  iDestruct "HIsSeg" as (? ? ? nℓ' ?) "(HIsSeg' & >#HLocs & HCancS)".
  iAssert (segment_next_location γ id nℓ') as "#HNextLoc'";
    first by eauto 6 with iFrame.
  iDestruct (segment_next_location_agree with "HNextLoc' HNextLoc") as %->.
  iClear "HNextLoc'".
  iDestruct "HIsSeg'" as "([[HMem'' Hnl] HMem'] & HCells)".
  destruct (decide (nl = InjRV #nextℓ)); subst.
  {
    wp_cmpxchg_suc. iDestruct "HClose" as "[_ HClose]".
    iMod ("HClose" with "[-]") as "HΦ".
    2: by iModIntro; wp_pures.
    iApply "HArrRestore".
    rewrite /is_normal_segment /is_segment /is_segment'.
    iExists pl, (InjRV _). iSplitL.
    by eauto 10 with iFrame.
    rewrite /is_valid_next. eauto 10 with iFrame.
  }
  {
    wp_cmpxchg_fail. iDestruct "HClose" as "[HClose _]".
    iMod ("HClose" with "[-]") as "AU".
    { iApply "HArrRestore".
      rewrite /is_normal_segment /is_segment /is_segment'.
      by eauto 20 with iFrame. }
    iModIntro. wp_pures. wp_lam. wp_pures.
    iApply "IH". done.
  }
Qed.

Theorem segment_move_prev_to_left_spec γ id (ℓ: loc) mpl:
  segment_location γ id ℓ -∗
  is_valid_prev γ id mpl -∗
  <<< ▷ is_infinite_array γ >>>
    segment_move_prev_to_left #ℓ mpl @ ⊤
  <<< ▷ is_infinite_array γ, RET #() >>>.
Proof.
  iIntros "#HSegLoc #HNewValidPrev". iIntros (Φ) "AU". wp_lam. wp_pures.
  rewrite /from_some. iLöb as "IH".

  awp_apply segment_prev_spec; iApply (aacc_aupd_abort with "AU"); first done.
  iIntros "HInfArr".
  iDestruct (is_segment_by_location with "HSegLoc HInfArr")
    as (? ?) "[HIsSeg HArrRestore]".
  iAaccIntro with "HIsSeg".
  { iIntros "HIsSeg !>". iSplitL; by [iApply "HArrRestore"|eauto]. }
  iIntros (?) "[HIsSeg #HPrevLoc] !>". iSplitL; first by iApply "HArrRestore".
  iIntros "AU !>".

  awp_apply segment_prev_read_spec; first done.
  iApply (aacc_aupd with "AU"); first done.
  iIntros "HInfArr".
  iDestruct (is_segment_by_location with "HSegLoc HInfArr")
    as (? ?) "[HIsSeg HArrRestore]".
  iAaccIntro with "HIsSeg".
  { iIntros "HIsSeg !>"; iSplitL; by [iApply "HArrRestore"|eauto]. }
  iIntros "[HIsSeg #HValidPrev] !>".

  iDestruct "HValidPrev" as "[[-> HCanc]|#HValidPrev]".
  { iRight. iSplitL. by iApply "HArrRestore". iIntros "HΦ !>". by wp_pures. }
  iDestruct "HValidPrev" as (opid opℓ) "(% & -> & #HPrevSegLoc & HNewCanc)".

  iLeft. iSplitL. by iApply "HArrRestore". iIntros "AU !>". wp_pures.
  iDestruct "HNewValidPrev" as "[[-> HNewCanc']|#HNewValidPrev']".
  2: iDestruct "HNewValidPrev'"
    as (npid nprevℓ) "(% & -> & #HNPrevSegLoc & HNewCanc')".
  all: wp_pures.
  {
    awp_apply segment_prev_spec; iApply (aacc_aupd_abort with "AU"); first done.
    iIntros "HInfArr".
    iDestruct (is_segment_by_location with "HSegLoc HInfArr")
      as (? ?) "[HIsSeg HArrRestore]".
    iAaccIntro with "HIsSeg".
    { iIntros "HIsSeg !>"; iSplitL; by [iApply "HArrRestore"|eauto]. }
    iIntros (pℓ') "[HIsSeg #HPrevLoc'] !>".
    iSplitL; first by iApply "HArrRestore". iIntros "AU !>".

    iDestruct (segment_prev_location_agree with "HPrevLoc' HPrevLoc") as %->.
    iClear "HPrevLoc'".

    wp_bind (CmpXchg _ _ _). iMod "AU" as "[HInfArr HClose]".
    iDestruct (is_segment_by_location_prev with "HSegLoc HInfArr")
      as (?) "[HIsSeg HArrRestore]".
    iDestruct "HIsSeg" as (pl) "HIsSeg".

    iDestructHIsSeg.
    iAssert (segment_prev_location γ id pℓ) as "#HPrevLoc'";
      first by eauto 6 with iFrame.
    iDestruct (segment_prev_location_agree with "HPrevLoc HPrevLoc'") as %->.
    iClear "HPrevLoc'".
    destruct (decide (pl = InjRV #opℓ)); subst.
    { wp_cmpxchg_suc. iDestruct "HClose" as "[_ HClose]".
      iMod ("HClose" with "[-]") as "HΦ".
      2: by iModIntro; wp_pures.
      iApply "HArrRestore".
      rewrite /is_segment /is_segment' /is_valid_prev.
      iExists dℓ, cℓ, pℓ, nℓ, _.
      iSplitR "HCancParts". 2: iSplitR; eauto 10 with iFrame.
      eauto 10 with iFrame.
    }
    { wp_cmpxchg_fail. iDestruct "HClose" as "[HClose _]".
      iMod ("HClose" with "[-]") as "AU".
      { iApply "HArrRestore".
        rewrite /is_segment /is_segment' /is_valid_prev.
        iExists dℓ, cℓ, pℓ, nℓ, _. eauto 10 with iFrame. }
      iModIntro. wp_pures. wp_lam. wp_pures.
      by iApply "IH".
    }
  }
  {
    awp_apply segment_id_spec. iApply (aacc_aupd_abort with "AU"); first done.
    iIntros "HInfArr".
    iDestruct (is_segment_by_location with "HNPrevSegLoc HInfArr")
      as (? ?) "[HIsSeg HArrRestore]".
    iAaccIntro with "HIsSeg"; iIntros "HIsSeg !>".
    { iSplitL; by [iApply "HArrRestore"|eauto]. }
    iSplitL; first by iApply "HArrRestore". iIntros "AU !>". wp_pures.

    awp_apply segment_id_spec. iApply (aacc_aupd with "AU"); first done.
    iIntros "HInfArr".
    iDestruct (is_segment_by_location with "HPrevSegLoc HInfArr")
      as (? ?) "[HIsSeg HArrRestore]".
    iAaccIntro with "HIsSeg"; iIntros "HIsSeg !>".
    { iSplitL; by [iApply "HArrRestore"|eauto]. }
    iAssert (▷ is_infinite_array γ)%I with "[-]" as "HInfArr".
    { by iApply "HArrRestore". }
    iFrame "HInfArr".

    destruct (bool_decide (opid <= npid)) eqn:E.
    { iRight. iIntros "HΦ !>". wp_pures. rewrite E. by wp_pures. }
    { iLeft. iIntros "AU !>". wp_pures. rewrite E. wp_pures.

  (* Mostly copy-pasted from above. *)
    awp_apply segment_prev_spec; iApply (aacc_aupd_abort with "AU"); first done.
    iIntros "HInfArr".
    iDestruct (is_segment_by_location with "HSegLoc HInfArr")
      as (? ?) "[HIsSeg HArrRestore]".
    iAaccIntro with "HIsSeg".
    { iIntros "HIsSeg !>"; iSplitL; by [iApply "HArrRestore"|eauto]. }
    iIntros (pℓ') "[HIsSeg #HPrevLoc'] !>".
    iSplitL; first by iApply "HArrRestore". iIntros "AU !>".

    iDestruct (segment_prev_location_agree with "HPrevLoc' HPrevLoc") as %->.
    iClear "HPrevLoc'".

    wp_bind (CmpXchg _ _ _). iMod "AU" as "[HInfArr HClose]".
    iDestruct (is_segment_by_location_prev with "HSegLoc HInfArr")
      as (?) "[HIsSeg HArrRestore]".
    iDestruct "HIsSeg" as (pl) "HIsSeg".

    iDestructHIsSeg.
    iAssert (segment_prev_location γ id pℓ) as "#HPrevLoc'";
      first by eauto 6 with iFrame.
    iDestruct (segment_prev_location_agree with "HPrevLoc HPrevLoc'") as %->.
    iClear "HPrevLoc'".
    destruct (decide (pl = InjRV #opℓ)); subst.
    { wp_cmpxchg_suc. iDestruct "HClose" as "[_ HClose]".
      iMod ("HClose" with "[-]") as "HΦ".
      2: by iModIntro; wp_pures.
      iApply "HArrRestore".
      rewrite /is_segment /is_segment' /is_valid_prev.
      iExists dℓ, cℓ, pℓ, nℓ, _.
      iSplitR "HCancParts". 2: iSplitR; eauto 10 with iFrame.
      iFrame. iSplit. 1: done. iRight. iClear "IH HValidPrev".
      iExists npid, _. eauto 10 with iFrame.
    }
    { wp_cmpxchg_fail. iDestruct "HClose" as "[HClose _]".
      iMod ("HClose" with "[-]") as "AU".
      { iApply "HArrRestore".
        rewrite /is_segment /is_segment' /is_valid_prev.
        iExists dℓ, cℓ, pℓ, nℓ, _. eauto 10 with iFrame. }
      iModIntro. wp_pures. wp_lam. wp_pures.
      by iApply "IH".
    } }
  }
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

Lemma segment_cancelled__cells_cancelled γ id:
  segment_is_cancelled γ id -∗
  [∗ list] id ∈ seq (id * Pos.to_nat segment_size)%nat (Pos.to_nat segment_size),
                       cell_is_cancelled γ id.
Proof.
  rewrite /segment_is_cancelled /cells_are_cancelled.
  iIntros "#HOld".
  iAssert ([∗ list] i ↦ v ∈ Vector.const true (Pos.to_nat segment_size),
           cell_is_cancelled' γ id i)%I with "[HOld]" as "#HOld'".
  {
    iApply big_sepL_mono. 2: done.
    iIntros (k y HEl). replace y with true. done.
    revert HEl. rewrite -vlookup_lookup'.
    case. intros ?. by rewrite Vector.const_nth.
  }
  rewrite big_sepL_forall.
  rewrite big_sepL_forall.
  iIntros (k x) "%".
  assert (k < Pos.to_nat segment_size)%nat as HKLt. {
    remember (seq _ _) as K. replace (Pos.to_nat segment_size) with (length K).
    apply lookup_lt_is_Some_1; by eauto.
    subst. by rewrite seq_length.
  }
  rewrite /cell_is_cancelled -(ias_cell_info_view_eq id k); try assumption.
  { iApply "HOld'". iPureIntro.
    rewrite -vlookup_lookup'. exists HKLt. done. }
  rewrite Nat.add_comm. rewrite -(@seq_nth (Pos.to_nat segment_size) _ _ O).
  2: by eauto.
  apply nth_lookup_Some with (d := O) in a.
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

Definition RemoveInv γ nlℓ plℓ :=
  (∃ nℓ nid, segment_location γ nid nℓ ∗ nlℓ ↦ SOMEV #nℓ ∗
                              (∃ pl, plℓ ↦ pl ∗ is_valid_prev γ nid pl))%I.

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

Theorem segment_is_removed_spec γ id (ℓ: loc):
  <<< ∀ pl nl, ▷ is_segment γ id ℓ pl nl >>>
    (segment_is_removed segment_size) #ℓ @ ⊤
  <<< ∃ (v: bool), ▷ is_segment γ id ℓ pl nl ∗
      (⌜v = false⌝ ∨ ⌜v = true⌝ ∧ segment_is_cancelled γ id), RET #v >>>.
Proof.
  iIntros (Φ) "AU". wp_lam. awp_apply segment_canc_spec.
  iApply (aacc_aupd_abort with "AU"); first done.
  iIntros (? ?) "HIsSeg". iAaccIntro with "HIsSeg".
  { iIntros "$ !>". by eauto. }
  iIntros (cℓ) "[$ #HCancLoc] !> AU !>".

  awp_apply segment_canc_read_spec; first done.
  iApply (aacc_aupd_commit with "AU"); first done.
  iIntros (? ?) "HIsSeg". iAaccIntro with "HIsSeg".
  { iIntros "$ !>". by eauto. }
  iIntros (cancelled) "[$ #HCells] !>".
  destruct (decide (cancelled = Pos.to_nat segment_size)); subst.
  2: {
    iExists false. iSplit; first by iLeft. iIntros "HΦ !>". wp_pures.
    rewrite bool_decide_eq_false_2; first by eauto.
    intros [=]; lia.
  }
  { iExists true. iSplit.
    2: iIntros "HΦ !>"; wp_pures; by rewrite positive_nat_Z bool_decide_eq_true_2.
    iRight. rewrite /segment_is_cancelled.
    iDestruct "HCells" as (cells) "[HCancelled %]".
    replace cells with (Vector.const true (Pos.to_nat segment_size)).
    1: by auto.

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
    apply Vector.const_nth.
  }
Qed.

Lemma segments_cancelled__cells_cancelled γ n m:
  ([∗ list] id ∈ seq n m, segment_is_cancelled γ id) -∗
   [∗ list] id ∈ seq (n * Pos.to_nat segment_size)%nat
   (m * Pos.to_nat segment_size)%nat,
  cell_is_cancelled γ id.
Proof.
  iIntros "#HSegCanc".
  iDestruct (big_sepL_mono with "HSegCanc") as "HSegCanc'".
  { intros ? ? _. simpl. iApply segment_cancelled__cells_cancelled. }
  by rewrite /= -big_sepL_bind seq_bind.
Qed.

Lemma move_cutoff id nid γ:
  (id < nid)%nat ->
  ([∗ list] j ∈ seq 0 (id * Pos.to_nat segment_size),
    cell_is_cancelled γ j ∨ cell_is_done j) -∗
  segment_is_cancelled γ id -∗
  ([∗ list] j ∈ seq (S id) (nid - S id), segment_is_cancelled γ j) -∗
  [∗ list] j ∈ seq 0 (nid * Pos.to_nat segment_size),
    cell_is_cancelled γ j ∨ cell_is_done j.
Proof.
  iIntros (HLt) "HLow HC HHigh".
  iAssert ([∗ list] j ∈ seq id (nid - id), segment_is_cancelled γ j)%I
    with "[HC HHigh]" as "HHigh".
  { replace (nid - id)%nat with (S (nid - S id)) by lia.
    simpl. iFrame. }
  rewrite -(seq_app (id * Pos.to_nat segment_size) _ (nid * _)).
  2: apply mult_le_compat_r; lia.
  rewrite big_sepL_app -Nat.mul_sub_distr_r /=. iFrame "HLow".
  iDestruct (segments_cancelled__cells_cancelled with "HHigh") as "HHigh".
  iApply big_sepL_mono. 2: done. iIntros; by iLeft.
Qed.

Lemma merge_cancelled_segments pid id nid γ:
  (pid < id)%nat -> (id < nid)%nat ->
  ([∗ list] j ∈ seq (S pid) (id - S pid), segment_is_cancelled γ j) -∗
  segment_is_cancelled γ id -∗
  ([∗ list] j ∈ seq (S id) (nid - S id), segment_is_cancelled γ j) -∗
  [∗ list] j ∈ seq (S pid) (nid - S pid), segment_is_cancelled γ j.
Proof.
  iIntros (HLt HLt') "HLow HC HHigh".
  iAssert ([∗ list] j ∈ seq id (nid - id), segment_is_cancelled γ j)%I
    with "[HC HHigh]" as "HHigh".
  { replace (nid - id)%nat with (S (nid - S id)) by lia.
    simpl. iFrame. }
  rewrite -(seq_app (id - S pid) _ (nid - S pid)). 2: lia. rewrite big_opL_app.
  replace (S pid + (id - S pid))%nat with id by lia.
  replace (nid - S pid - (id - S pid))%nat with (nid - id)%nat by lia.
  iFrame.
Qed.

Theorem remove_first_loop_spec γ (plℓ nlℓ: loc):
  RemoveInv γ nlℓ plℓ -∗
  <<< ▷ is_infinite_array γ >>>
    (segment_remove_first_loop segment_size) #plℓ #nlℓ @ ⊤
  <<< ▷ is_infinite_array γ ∗ RemoveInv γ nlℓ plℓ, RET #() >>>.
Proof.
  iIntros "RemoveInv". iIntros (Φ) "AU". wp_lam. wp_pures.
  iLöb as "IH". wp_bind (! _)%E.
  iDestruct "RemoveInv" as (? nid) "(#HNextSegLoc & Hnlℓ & Hplℓ)".
  iDestruct "Hplℓ" as (?) "[Hplℓ [[-> #HCanc]|HVplℓ]]".
  { iMod "AU" as "[HInfArr [_ HClose]]".
    wp_load.
    iMod ("HClose" with "[-]") as "HΦ".
    { iFrame "HInfArr". rewrite /RemoveInv /is_valid_prev.
      iExists _, _. iFrame "Hnlℓ HNextSegLoc".
      iExists _. iFrame "Hplℓ". iLeft. iSplit; done. }
    iModIntro.
    by wp_pures. }
  iDestruct "HVplℓ" as (pid ?) "(% & -> & #HPrevSegLoc & #HSegCanc)".
  wp_load. wp_pures. rewrite /from_some. wp_load. wp_pures. wp_load.

  awp_apply segment_move_next_to_right_spec; first done.
  { iExists _, _. eauto with iFrame. }
  iApply (aacc_aupd_abort with "AU"); first done.
  iIntros "HInfArr". iAaccIntro with "HInfArr"; iIntros "$ !>".
  { eauto with iFrame. }
  iIntros "AU !>". wp_pures.

  awp_apply segment_is_removed_spec. iApply (aacc_aupd with "AU"); first done.
  iIntros "HInfArr".
  iDestruct (is_segment_by_location with "HPrevSegLoc HInfArr")
    as (? ?) "[HIsSeg HArrRestore]".
  iAaccIntro with "HIsSeg".
  { iIntros "HIsSeg !>". iDestruct ("HArrRestore" with "HIsSeg") as "$".
    by eauto with iFrame. }
  iIntros (b) "[HIsSeg HCanc] !>".
  iDestruct ("HArrRestore" with "HIsSeg") as "$".
  iDestruct "HCanc" as "[->|[-> #HSegCanc']]".
  { iRight. iSplitL.
    { rewrite /RemoveInv. iExists _, _. iFrame "HNextSegLoc Hnlℓ".
      iExists _. iFrame "Hplℓ". rewrite /is_valid_prev.
      iRight. iClear "IH". iExists _, _.
      eauto with iFrame.
    }
    iIntros "HΦ !>". by wp_pures. }
  iLeft. iIntros "AU !>". wp_pures.

  awp_apply segment_prev_spec. iApply (aacc_aupd_abort with "AU"); first done.
  iIntros "HInfArr".
  iDestruct (is_segment_by_location with "HPrevSegLoc HInfArr")
    as (? ?) "[HIsSeg HArrRestore]".
  iAaccIntro with "HIsSeg".
  { iIntros "HIsSeg !>". iDestruct ("HArrRestore" with "HIsSeg") as "$".
    by eauto with iFrame. }
  iIntros (cℓ) "[HIsSeg #HPrevLoc] !>".
  iDestruct (bi.later_wand with "HArrRestore HIsSeg") as "$".
  iIntros "AU !>".

  awp_apply segment_prev_read_spec; first done.
  iApply (aacc_aupd_abort with "AU"); first done.
  iIntros "HInfArr".
  iDestruct (is_segment_by_location with "HPrevSegLoc HInfArr")
    as (? ?) "[HIsSeg HArrRestore]".
  iAaccIntro with "HIsSeg".
  { iIntros "HIsSeg !>". iDestruct ("HArrRestore" with "HIsSeg") as "$".
    by eauto with iFrame. }
  iIntros "[HIsSeg #HValidPrev] !>".
  iDestruct (bi.later_wand with "HArrRestore HIsSeg") as "$".
  iIntros "AU !>".
  wp_store. wp_lam. wp_pures.
  iApply ("IH" with "[-AU]"). 2: by auto.

  iClear "IH". rewrite /RemoveInv.
  iExists _, _. iFrame "HNextSegLoc Hnlℓ". iExists _. iFrame "Hplℓ".

  iDestruct "HValidPrev" as "[[-> #HOldCanc]|HValidPrev]".
  { iLeft; iSplit; first done.
    iApply move_cutoff; try done.
    lia. }
  { iRight. iDestruct "HValidPrev"
      as (pid' prevℓ') "(% & -> & #HNewPrevSegLoc & #HNewPrevCanc)".
    iExists pid', prevℓ'. repeat iSplit; try done.
    iPureIntro; lia.

    iApply (merge_cancelled_segments pid' pid nid); try done; lia.
  }
Qed.

Theorem remove_second_loop_spec γ (plℓ nlℓ: loc):
  RemoveInv γ nlℓ plℓ -∗
  <<< ▷ is_infinite_array γ >>>
    (segment_remove_second_loop segment_size) #plℓ #nlℓ @ ⊤
  <<< ▷ is_infinite_array γ ∗ RemoveInv γ nlℓ plℓ, RET #() >>>.
Proof.
  iIntros "RemoveInv". iIntros (Φ) "AU". wp_lam. wp_pures.
  rewrite /from_some. iLöb as "IH". wp_bind (! _)%E.
  iDestruct "RemoveInv" as (? nid) "(#HNextSegLoc & Hnlℓ & Hplℓ)".
  iDestruct "Hplℓ" as (pl) "[Hplℓ #HValidPrev]".
  wp_load. wp_pures.

  awp_apply segment_is_removed_spec.
  iApply (aacc_aupd with "AU"); first done.
  iIntros "HInfArr".
  iDestruct (is_segment_by_location with "HNextSegLoc HInfArr")
    as (? ?) "[HIsSeg HArrRestore]".
  iAaccIntro with "HIsSeg".
  { iIntros "HIsSeg". iDestruct ("HArrRestore" with "HIsSeg") as "$".
    by eauto with iFrame. }
  iIntros (?) "[HIsSeg HIsRemoved] !>".
  iDestruct (bi.later_wand with "HArrRestore HIsSeg") as "$".

  iDestruct "HIsRemoved" as "[->|[-> #HSegCanc]]".
  { iRight. iSplitL.
    2: by iIntros "HΦ"; iModIntro; wp_pures.
    iExists _, _. iFrame "HNextSegLoc Hnlℓ".
    iExists _. iFrame "Hplℓ HValidPrev". }
  iLeft. iIntros "AU !>". wp_pures.

  awp_apply segment_next_spec. iApply (aacc_aupd_abort with "AU"); first done.
  iIntros "HInfArr".
  iDestruct (is_segment_by_location with "HNextSegLoc HInfArr")
    as (? ?) "[HIsSeg HArrRestore]".
  iAaccIntro with "HIsSeg".
  { iIntros "HIsSeg". iDestruct ("HArrRestore" with "HIsSeg") as "$".
    by eauto with iFrame. }
  iIntros (?) "[HIsSeg #HNextLoc] !>".
  iDestruct (bi.later_wand with "HArrRestore HIsSeg") as "$".
  iIntros "AU !>".

  awp_apply segment_next_read_spec; first done.
  iApply (aacc_aupd with "AU"); first done.
  iIntros "HInfArr".
  iDestruct (segment_by_location with "HNextSegLoc HInfArr")
    as "[[HH HArrRestore]|[HH HArrRestore]]".
  2: {
    iDestruct "HH" as (?) "HIsSeg".
    iAaccIntro with "HIsSeg".
    { iIntros "HIsSeg !>". iSplitL "HArrRestore HIsSeg". 2: by eauto with iFrame.
      iApply "HArrRestore". iExists _. iFrame "HIsSeg". }
    iIntros "HIsSeg !>". iRight. iSplitL.
    2: by iIntros "HΦ !>"; wp_pures.
    iSplitL "HArrRestore HIsSeg".
    { iApply "HArrRestore". iExists _. by iAssumption. }
    rewrite /RemoveInv. iExists _, _. iFrame "Hnlℓ HNextSegLoc".
    iExists _. iFrame "Hplℓ HValidPrev".
  }
  iDestruct "HH" as (? ?) "(HIsSeg & #HValidNext)".
  iAaccIntro with "HIsSeg".
  { iIntros "HIsSeg !>". iSplitR "Hnlℓ Hplℓ". 2: by eauto with iFrame.
    iApply "HArrRestore". iExists _, _. by iFrame. }
  iIntros "HIsSeg !>". iLeft. iSplitR "Hnlℓ Hplℓ".
  { iApply "HArrRestore". iExists _, _. by iFrame. }
  iIntros "AU !>". wp_pures.

  iDestruct (can_not_be_tail_if_has_next with "HValidNext") as "#HNotTail".
  iDestruct "HValidNext" as (? ?) "(% & -> & _)".
  wp_pures.

  awp_apply segment_next_spec. iApply (aacc_aupd_abort with "AU"); first done.
  iIntros "HInfArr".
  iDestruct (is_segment_by_location with "HNextSegLoc HInfArr")
    as (? ?) "[HIsSeg HArrRestore]".
  iAaccIntro with "HIsSeg".
  { iIntros "HIsSeg !>". iSplitR "Hnlℓ Hplℓ". 2: by eauto with iFrame.
    iDestruct ("HArrRestore" with "HIsSeg") as "$". }
  iIntros (?) "[HIsSeg HNextLoc'] !>".
  iDestruct (bi.later_wand with "HArrRestore HIsSeg") as "$".
  iDestruct (segment_next_location_agree with "HNextLoc' HNextLoc") as %->.
  iClear "HNextLoc'".
  iIntros "AU !>".

  awp_apply segment_next_read_spec; first by iAssumption.
  iApply (aacc_aupd_abort with "AU"); first done.
  iIntros "HInfArr".
  iDestruct (normal_segment_by_location with "HNextSegLoc HNotTail HInfArr")
    as "[HNormSeg HArrRestore]".
  iDestruct "HNormSeg" as (? ?) "[HIsSeg >#HValidNext]".
  iAaccIntro with "HIsSeg".
  all: iIntros "HIsSeg !>"; iSplitR "Hnlℓ Hplℓ"; first by
    iApply "HArrRestore"; iExists _, _; by iFrame.
  by eauto with iFrame.
  iIntros "AU !>".

  wp_store. wp_load. wp_load.

  iDestruct "HValidNext" as (nid' ?) "(% & -> & #HNewNextSegLoc & #HNewSegCanc)".
  wp_pures.

  iAssert (is_valid_prev γ nid' pl) as "#HNewValidPrev".
  { iDestruct "HValidPrev" as "[[-> HCanc]|HValidPrev]".
    { iLeft; iSplitR; first done. iApply move_cutoff; try done. lia. }
    { iDestruct "HValidPrev" as (pid prevℓ) "(% & -> & #HSegLoc & #HPrevCanc)".
      iRight; iExists pid, prevℓ; repeat iSplit; try done. iPureIntro; lia.
      iApply merge_cancelled_segments; try done; lia. }
  }

  awp_apply segment_move_prev_to_left_spec; try done.
  iApply (aacc_aupd_abort with "AU"); first done.
  iIntros "HInfArr". iAaccIntro with "HInfArr"; iIntros "$ !> AU !>".
  by iFrame.

  wp_pures. wp_lam. wp_pures. iApply ("IH" with "[-AU]"); try done. iClear "IH".
  rewrite /RemoveInv.
  iExists _, _. iFrame "Hnlℓ HNewNextSegLoc". iExists _; by iFrame.
Qed.

Theorem remove_segment_spec γ id (ℓ: loc):
  segment_is_cancelled γ id -∗
  segment_location γ id ℓ -∗
  <<< ▷ is_infinite_array γ >>>
    (segment_remove segment_size) #ℓ @ ⊤
  <<< ∃ v, ▷ is_infinite_array γ ∗ (⌜v = NONEV⌝ ∨
                                    ∃ p nℓ nid, segment_location γ nid nℓ ∗
                                                ⌜v = SOMEV (p, #nℓ)⌝ ∗
                                                is_valid_prev γ nid p),
    RET v >>>.
Proof.
  iIntros "#HSegCanc #HSegLoc". iIntros (Φ) "AU". wp_lam.

  awp_apply segment_prev_spec. iApply (aacc_aupd_abort with "AU"); first done.
  iIntros "HInfArr".
  iDestruct (is_segment_by_location with "HSegLoc HInfArr")
    as (? ?) "[HIsSeg HArrRestore]".
  iAaccIntro with "HIsSeg".
  { iIntros "HIsSeg". iSpecialize ("HArrRestore" with "HIsSeg").
    by eauto with iFrame. }
  iIntros (?) "[HIsSeg #HPrevLoc]".
  iDestruct (bi.later_wand with "HArrRestore HIsSeg") as "$".
  iIntros "!> AU !>".

  awp_apply segment_prev_read_spec; first done.
  iApply (aacc_aupd_abort with "AU"); first done.
  iIntros "HInfArr".
  iDestruct (is_segment_by_location with "HSegLoc HInfArr")
    as (? ?) "[HIsSeg HArrRestore]".
  iAaccIntro with "HIsSeg".
  { iIntros "HIsSeg". iDestruct ("HArrRestore" with "HIsSeg") as "$". by eauto. }
  iIntros "[HIsSeg #HValidPrev]".
  iDestruct (bi.later_wand with "HArrRestore HIsSeg") as "$".
  iIntros "!> AU !>".

  wp_alloc plℓ as "Hplℓ". wp_pures.

  awp_apply segment_next_spec. iApply (aacc_aupd_abort with "AU"); first done.
  iIntros "HInfArr".
  iDestruct (is_segment_by_location with "HSegLoc HInfArr")
    as (? ?) "[HIsSeg HArrRestore]".
  iAaccIntro with "HIsSeg".
  { iIntros "HIsSeg". iDestruct ("HArrRestore" with "HIsSeg") as "$".
    by eauto with iFrame. }
  iIntros (?) "[HIsSeg #HNextLoc]".
  iDestruct (bi.later_wand with "HArrRestore HIsSeg") as "$".
  iIntros "!> AU !>".

  awp_apply segment_next_read_spec without "Hplℓ"; first done.
  iApply (aacc_aupd with "AU"); first done.
  iIntros "HInfArr".
  iDestruct (segment_by_location with "HSegLoc HInfArr")
    as "[[HIsNSeg HArrRestore]|[HIsTSeg HArrRestore]]".
  2: {
    iDestruct "HIsTSeg" as (pl) "HIsSeg".
    iAaccIntro with "HIsSeg". all: iIntros "HIsSeg !>".
    { iSplitL. 2: by eauto. iApply "HArrRestore". iExists _. iFrame. }
    iRight. iExists _. iSplitL. iSplitL.
    { iApply "HArrRestore". iExists _. iFrame. }
    { iLeft; done. }
    iIntros "HΦ !> Hplℓ". wp_bind (ref _)%E. wp_alloc nlℓ as "Hnlℓ". wp_pures.
    wp_load. wp_pures. done.
  }

  iDestruct "HIsNSeg" as (? ?) "(HIsSeg & #HValidNext)".
  iAaccIntro with "HIsSeg"; iIntros "HIsSeg !>".
  { iSplitL. 2: by eauto. iApply "HArrRestore".
    iExists _, _. iFrame "HIsSeg HValidNext HNotTail". }
  iLeft. iSplitL.
  { iApply "HArrRestore". iExists _, _. iFrame "HIsSeg HValidNext HNotTail". }
  iIntros "AU".
  iIntros "!> Hplℓ".
  wp_alloc nlℓ as "Hnlℓ".

  iAssert (RemoveInv γ nlℓ plℓ) with "[Hplℓ Hnlℓ]" as "RemoveInv".
  { iDestruct "HValidNext"
      as (nid nextℓ) "(% & -> & #HNextSegLoc & HNextSegCanc)".
    iExists nextℓ, nid. iFrame "HNextSegLoc". iFrame.
    iDestruct "HValidPrev" as "[(-> & #HPrevCanc)|HH]".
    { iExists (InjLV #()). iFrame. iLeft. iSplitL; first done.
      iApply move_cutoff; try done. lia. }
    {
      iDestruct "HH" as (pid prevℓ) "(% & -> & #HPrevSegLoc & #HPrevSegCanc)".
      iExists _. iFrame. iRight. iExists _, _. iFrame "HPrevSegLoc".
      iSplitR. by iPureIntro; lia. iSplitR; first done.
      iApply merge_cancelled_segments; try done; lia. }
  }
  wp_pures.
  iClear "HSegCanc HSegLoc HPrevLoc HValidPrev HNextLoc HValidNext".
  revert cell_invariant_persistent cell_is_done_persistent; clear; intros ? ?.
  wp_bind (! _)%E. iDestruct "RemoveInv" as (nℓ nid) "(#HSegLoc & Hnlℓ & Hplℓ)".
  wp_load.
  iAssert (RemoveInv γ nlℓ plℓ) with "[Hnlℓ Hplℓ]" as "RemoveInv".
  1: by rewrite /RemoveInv; eauto with iFrame.
  wp_pures. iClear "HSegLoc".
  revert cell_invariant_persistent cell_is_done_persistent; clear; intros ? ?.

  awp_apply (remove_first_loop_spec with "RemoveInv").
  iApply (aacc_aupd_abort with "AU"); first done.
  iIntros "HInfArr". iAaccIntro with "HInfArr".
  iIntros "$"; by eauto with iFrame.
  iIntros "[$ RemoveInv] !> AU !>". wp_pures.

  iDestruct "RemoveInv" as (? ?) "(#HSegLoc & Hnlℓ & Hplℓ)".
  iDestruct "Hplℓ" as (?) "[Hplℓ #HValidPrev]".
  wp_load. wp_load. rewrite /from_some. wp_pures.

  awp_apply (segment_move_prev_to_left_spec); try done.
  iApply (aacc_aupd_abort with "AU"); first done. iIntros "HInfArr".
  iAaccIntro with "HInfArr"; iIntros "$"; first by eauto with iFrame.
  iIntros "!> AU !>". wp_pures.

  iAssert (RemoveInv γ nlℓ plℓ) with "[Hnlℓ Hplℓ]" as "RemoveInv".
  { iExists _, _. iFrame "HSegLoc Hnlℓ". iExists _. by iFrame. }
  iClear "HSegLoc HValidPrev".

  awp_apply (remove_second_loop_spec with "RemoveInv").
  iApply (aacc_aupd_commit with "AU"); first done.
  iIntros "HInfArr". iAaccIntro with "HInfArr".
  iIntros "$"; by eauto with iFrame.
  iIntros "[$ RemoveInv] !>".

  iDestruct "RemoveInv" as (nℓ nid) "(#HSegLoc & Hnlℓ & Hplℓ)".
  iDestruct "Hplℓ" as (p) "[Hplℓ #HValidPrev]".

  iExists _. iSplitR.
  2: iIntros "HΦ !>"; wp_pures; wp_load; wp_pures; wp_load; wp_pures; done.
  iRight. iExists _, _, _. iFrame "HSegLoc HValidPrev". done.
Qed.

Lemma replicate_op {A: ucmraT} (a b: A) n:
  replicate n (a ⋅ b) = replicate n a ⋅ replicate n b.
Proof. apply list_eq. induction n; simpl. done. case; done. Qed.

Lemma pair_op_2 {A: ucmraT} {B: cmraT} (b b': B):
  (ε, b ⋅ b') ≡ ((ε: A), b) ⋅ (ε, b').
Proof. by rewrite -pair_op ucmra_unit_left_id. Qed.

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
  apply big_opL_forall; try apply _.
  intros ? ?; rewrite lookup_replicate; case; by intros ->.
Qed.

Lemma big_opL_irrelevant_element'
      (M: ofeT) (o: M -> M -> M) (H': Monoid o)
      {A: Type} (P: nat -> M) (l: list A):
  ([^o list] i ↦ k ∈ l, P i)%I = ([^o list] i ∈ seq 0 (length l), P i%nat)%I.
Proof. by rewrite -big_opL_irrelevant_element. Qed.

Lemma segment_info_to_cell_info l γ id:
  own γ (◯ ias_segment_info id (ε, l)) ≡
  (([∗ list] i ↦ e ∈ l, own γ (◯ ias_cell_info' id i e)) ∗
  own γ (◯ ias_segment_info id (ε, replicate (length l)%nat ε)))%I.
Proof.
  replace (ias_segment_info id (ε, l)) with
      (ias_segment_info id (ε, replicate O ε ++ l)).
  2: by auto.
  by rewrite segment_info_to_cell_info'.
Qed.

(* from https://gitlab.mpi-sws.org/iris/iris/commit/aa5a89e08b2cad8b7f780f296b78ea27ab8f6246?merge_request_iid=305 *)
Global Instance bupd_homomorphism :
  MonoidHomomorphism bi_sep bi_sep (flip (⊢)) (bupd (PROP:=iProp)).
Proof. split; [split|]; try apply _. apply bupd_sep. apply bupd_intro. Qed.
Lemma big_sepL_bupd {A} (Φ : nat → A → iProp) l :
  ([∗ list] k↦x ∈ l, |==> Φ k x) ⊢ |==> [∗ list] k↦x ∈ l, Φ k x.
Proof. by rewrite (big_opL_commute _). Qed.

Lemma algebra_append_new_segment p γ segments:
  own γ (● segments) -∗
      |==> ∃ z, own γ (● (segments ++ [z]))
                            ∗ segment_locations γ (length segments) p
                            ∗ cell_cancellation_parts γ (length segments)
                                (Vector.const false _)
                            ∗ [∗ list] j ∈ seq 0 (Pos.to_nat segment_size),
                                cell_cancellation_handle' γ (length segments) j.
Proof.
  iIntros "HOwn".
  iMod (own_update with "HOwn") as "[HAuth HFrag]".
  {
    apply auth_update_alloc
      with (a' :=
              (segments ++ [(Some (to_agree p),
                 replicate (Pos.to_nat segment_size)
                           (Some (Cinr 1%Qp)))])
           ).
    remember (Some _, replicate _ _) as K.
    eapply transitivity.
    apply list_append_local_update with (z := [K]); subst.
    { intros n.
      apply list_lookup_validN; case; simpl; try done.
      apply Some_validN. split; simpl; try done.
      apply list_lookup_validN; induction (Pos.to_nat segment_size);
        case; done. }
    subst; apply local_update_refl.
  }
  remember (Some _, _) as K.
  replace (replicate _ _ ++ _) with (ias_segment_info (length segments) K).
  all: subst K. 2: rewrite /ias_segment_info.
  2: apply list_eq; induction (length segments); case; done.
  iModIntro. iExists _. iFrame.
  replace (Some _, replicate _ _) with
      ((Some (to_agree p), ε)
         ⋅ (ε, replicate (Pos.to_nat segment_size) (Some (Cinr 1%Qp)))) by done.
  rewrite ias_segment_info_op auth_frag_op own_op.
  iDestruct "HFrag" as "[HSegLoc HCanc]".
  rewrite /segment_locations. iFrame "HSegLoc".
  replace (1%Qp) with ((1/4)%Qp ⋅ (3/4)%Qp) by apply Qp_quarter_three_quarter.
  rewrite Cinr_op Some_op replicate_op pair_op_2 ias_segment_info_op auth_frag_op own_op.
  iDestruct "HCanc" as "[HCancParts HCancHandles]".
  iSplitL "HCancParts".
  {
    rewrite /cell_cancellation_parts. clear.
    remember (length segments) as M.
    remember (Pos.to_nat segment_size) as N. clear.
    iApply (big_sepL_mono
              (fun k _ => own γ (◯ ias_cell_info' M k (Some (Cinr (1/4)%Qp))))).
    { intros ? ? HEl.
      apply vlookup_lookup' in HEl.
      destruct HEl as [? HEl].
      rewrite Vector.const_nth in HEl.
      subst.
      iIntros "HOk". iApply "HOk".
    }
    rewrite big_opL_irrelevant_element'.
    rewrite segment_info_to_cell_info.
    rewrite vec_to_list_length.
    iDestruct "HCancParts" as "[HLst _]".
    rewrite big_opL_replicate_irrelevant_element.
    rewrite big_opL_irrelevant_element'.
    by rewrite replicate_length.
  }
  rewrite segment_info_to_cell_info /cell_cancellation_handle'.
  iDestruct "HCancHandles" as "[HCancHandles _]".
  rewrite big_opL_replicate_irrelevant_element.
  rewrite big_opL_irrelevant_element'.
  by rewrite replicate_length.
Qed.

Lemma alloc_tail γ ℓ dℓ cℓ pℓ nℓ pl segments:
  cell_init ∗
  own γ (● segments) ∗
  nℓ ↦ NONEV ∗ pℓ ↦ pl ∗ is_valid_prev γ (length segments) pl ∗
  dℓ ↦∗ replicate (Z.to_nat (Z.pos segment_size)) NONEV ∗
  cℓ ↦ #0 ∗ ℓ ↦ (#(length segments), #cℓ, #dℓ, (#pℓ, #nℓ))
  ==∗
  ∃ z, own γ (● (segments ++ [z])) ∗ segment_location γ (length segments) ℓ ∗
           is_tail_segment γ ℓ (length segments).
Proof.
  iIntros "(#HCellInit & HAuth & Hnℓ & Hpℓ & #HValidPrev & Hdℓ & Hcℓ & Hℓ)".
  iDestruct (algebra_append_new_segment (ℓ, (dℓ, cℓ), (pℓ, nℓ)) with "HAuth")
    as ">HH".
  iDestruct "HH" as (z) "(HAuth & #HSegLocs & HCancParts & HCancHandles)".

  iAssert (segment_location γ (length segments) ℓ) as "#HSegLoc";
    first by eauto 10 with iFrame.

  iCombine "Hdℓ" "HCancHandles" as "HCellInfo".
  rewrite /array big_opL_replicate_irrelevant_element big_opL_irrelevant_element'.
  rewrite replicate_length Z2Nat.inj_pos -big_sepL_sep.
  iAssert ([∗ list] x ∈ seq 0 (Pos.to_nat segment_size),
           |==> cell_invariant γ (length segments * Pos.to_nat segment_size + x) (dℓ +ₗ x))%I
    with "[HCellInfo]" as "HCellInfo".
  {
    iApply (big_sepL_impl with "HCellInfo").
    iModIntro. iIntros (a i HIn) "[Hℓ HCancHandle]".
    iApply ("HCellInit" with "[HCancHandle]").
    2: done.
    rewrite /cell_cancellation_handle.
    rewrite -(ias_cell_info_view_eq (length segments) i); try done.
    2: lia.
    replace (Pos.to_nat segment_size)
      with (length (seq 0 (Pos.to_nat segment_size)))
      by (rewrite seq_length; auto).
    apply lookup_lt_is_Some.
    assert (a < length (seq 0 (Pos.to_nat segment_size)))%nat as HLt.
    { apply lookup_lt_is_Some; by eexists. }
    assert (a = i) as ->.
    { apply nth_lookup_Some with (d := O) in HIn.
      rewrite seq_nth in HIn. done.
      rewrite seq_length in HLt. done. }
    by eexists.
  }
  iDestruct (big_sepL_bupd with "HCellInfo") as ">HCellInfo".

  iExists z. iFrame "HAuth HSegLoc".
  iExists pl. rewrite /is_segment. iExists dℓ, cℓ, pℓ, nℓ, O.
  iFrame. iFrame "HValidPrev HSegLocs".
  iExists (Vector.const false _). iFrame. iModIntro; iSplit.
  - iPureIntro; induction (Pos.to_nat segment_size); done.
  - rewrite /cells_are_cancelled.
    iApply (big_sepL_mono (fun _ _ => True%I)).
    2: by iApply big_sepL_forall.
    intros ? ? HEl.
    apply vlookup_lookup' in HEl. destruct HEl as [? HEl].
    rewrite Vector.const_nth in HEl. by subst.
Qed.

Theorem initial_segment_spec:
  {{{ cell_init }}}
    (new_segment segment_size) #O NONEV
  {{{ γ (ℓ: loc), RET #ℓ; is_infinite_array γ ∗ segment_location γ O ℓ }}}.
Proof.
  iIntros (Φ) "#HCellInit HPost". wp_lam. wp_pures.
  wp_alloc nℓ as "Hnℓ". wp_alloc pℓ as "Hpℓ".
  wp_alloc dℓ as "Hdℓ"; first by lia. wp_alloc cℓ as "Hcℓ". wp_pures.
  rewrite -wp_fupd.
  wp_alloc ℓ as "Hℓ".
  iMod (own_alloc (● [] ⋅ ◯ [])) as (γ) "[HOwn _]".
  { apply auth_both_valid; split; try done. apply list_lookup_valid; by case. }

  iDestruct (alloc_tail with "[-HPost]") as ">HTail".
  { iFrame "HOwn Hnℓ Hpℓ Hcℓ Hdℓ Hℓ HCellInit". iLeft. iSplit; done. }

  iApply "HPost".

  iDestruct "HTail" as (z) "(HAuth & $ & HTailSeg)".
  rewrite /is_infinite_array.
  iExists []; simpl. iSplitR; first done.
  iSplitL "HTailSeg".
  - by iExists _.
  - iExists _; iFrame. by iPureIntro.
Qed.

Lemma seq_lookup start len n:
  (n < len)%nat ->
  seq start len !! n = Some (start + n)%nat.
Proof.
  intros HLt.
  replace len with (length (seq start len)) in HLt.
  2: by rewrite seq_length.
  destruct (lookup_lt_is_Some_2 _ _ HLt) as [? HOk].
  rewrite HOk.
  apply nth_lookup_Some with (d := O) in HOk.
  rewrite -(@seq_nth len _ _ O); auto.
  by rewrite seq_length in HLt.
Qed.

Lemma seq_lookup' start len n x:
  seq start len !! n = Some x ->
  x = (start + n)%nat /\ (n < len)%nat.
Proof.
  intros HSome.
  assert (is_Some (seq start len !! n)) as HIsSome by eauto.
  move: (lookup_lt_is_Some_1 _ _ HIsSome).
  rewrite seq_length.
  apply nth_lookup_Some with (d := O) in HSome.
  intros.
  rewrite seq_nth in HSome; auto.
Qed.

Lemma try_swap_tail γ id ℓ:
  segment_location γ id ℓ -∗ is_infinite_array γ -∗
  ((is_normal_segment γ ℓ id ∗ (is_normal_segment γ ℓ id -∗ is_infinite_array γ)) ∨
   (is_tail_segment γ ℓ id ∗ ∃ segments', ⌜S id = length segments'⌝ ∗
                                          own γ (● segments') ∗
                    (∀ ℓ' z, is_normal_segment γ ℓ id -∗
                             is_tail_segment γ ℓ' (S id) -∗
                             own γ (● (segments' ++ [z])) -∗
                             is_infinite_array γ))).
Proof.
  iIntros "#HSegLoc HInfArr".
  iDestruct "HInfArr" as (segments) "[HNormSegs [HTailSeg HAuth]]".
  iDestruct "HAuth" as (segments') "[% HAuth]".
  destruct (le_lt_dec (length segments) id).
  { inversion l; subst.
    2: {
      rewrite /segment_location /segment_locations.
      iDestruct "HSegLoc" as (? ? ? ?) "#HSeg".
      iDestruct (own_valid_2 with "HAuth HSeg")
        as %[HValid _]%auth_both_valid.
      exfalso. revert HValid. rewrite list_lookup_included.
      intro HValid. specialize (HValid (S m)).
      rewrite ias_segment_info_lookup in HValid.
      assert (length segments' <= S m)%nat as HIsNil by lia.
      apply lookup_ge_None in HIsNil. rewrite HIsNil in HValid.
      apply option_included in HValid.
      destruct HValid as [[=]|[a [b [_ [[=] _]]]]].
    }
    iDestruct "HTailSeg" as (ℓ' pl) "HIsSeg".
    destruct (decide (ℓ = ℓ')); subst.
    2: {
      iDestruct "HIsSeg" as (? ? ? ? ?) "[_ [HLocs _]]".
      iAssert (segment_location γ (length segments) ℓ') as "#HLoc";
        first by eauto 6.
      iDestruct (segment_location_agree with "HSegLoc HLoc") as %->.
      contradiction.
    }
    iRight.
    iSplitL "HIsSeg"; first by rewrite /is_tail_segment; eauto with iFrame.
    iExists segments'. iFrame. iSplitR; first done.
    iIntros (ℓ'' z) "HExTail HNewTail HAuth". rewrite /is_infinite_array.
    iExists (segments ++ [ℓ']). iFrame "HNormSegs". simpl. rewrite -plus_n_O.
    iFrame "HExTail". iSplitR "HAuth"; iExists _;
                        rewrite app_length /= Nat.add_1_r.
    done.
    iFrame. rewrite app_length /= Nat.add_1_r. auto.
  }
  apply lookup_lt_is_Some_2 in l. destruct l as [x Hx].
  iDestruct (big_sepL_lookup_acc with "[HNormSegs]") as "[HIsSeg HRestSegs]".
  2: by iApply "HNormSegs".
  apply Hx.
  simpl.
  iLeft.
  destruct (decide (ℓ = x)); subst.
  2: {
    iDestruct "HIsSeg" as (pl nl) "[HIsSeg #HValNext]".
    iDestruct "HIsSeg" as (? ? ? ? ?) "[_ [HLocs _]]".
    iAssert (segment_location γ id x) as "#HLoc";
      first by eauto 6.
    iDestruct (segment_location_agree with "HSegLoc HLoc") as %->.
    contradiction.
  }
  iFrame.
  iIntros "HNormSeg". rewrite /is_infinite_array.
  iExists segments. iFrame. iSplitR "HAuth".
  { by iApply "HRestSegs". }
  eauto 10 with iFrame.
Qed.

Theorem find_segment_spec γ (ℓ: loc) (id fid: nat):
  cell_init -∗
  segment_location γ id ℓ -∗
  <<< ▷ is_infinite_array γ >>>
    (find_segment segment_size) #ℓ #fid @ ⊤
  <<< ∃ (id': nat) (ℓ': loc), ▷ is_infinite_array γ ∗
        segment_location γ id' ℓ' ∗
        ((⌜fid <= id⌝ ∧ ⌜id = id'⌝) ∨
         ⌜id <= fid⌝ ∧ ⌜fid <= id'⌝ ∗
          [∗ list] i ∈ seq fid (id' - fid), segment_is_cancelled γ i),
      RET #ℓ' >>>.
Proof.
  iIntros "#HCellInit #HHeadLoc". iIntros (Φ) "AU".

  iLöb as "IH" forall (id ℓ) "HHeadLoc". wp_lam. wp_pures.

  awp_apply segment_id_spec. iApply (aacc_aupd with "AU"); first done.
  iIntros "HInfArr".
  iDestruct (is_segment_by_location with "HHeadLoc HInfArr")
    as (? ?) "[HIsSeg HArrRestore]".
  iAaccIntro with "HIsSeg"; iIntros "HIsSeg".
  { iDestruct ("HArrRestore" with "HIsSeg") as "$". by eauto with iFrame. }
  iDestruct (bi.later_wand with "HArrRestore HIsSeg") as "$".
  destruct (decide (fid <= id)) eqn:E.
  { iRight. iModIntro. iExists _, _. iFrame "HHeadLoc".
    iSplit. iLeft; repeat iSplit; by iPureIntro.
    iIntros "HΦ !>". wp_pures. rewrite bool_decide_decide E. by wp_pures. }
  iLeft. iIntros "!> AU !>". wp_pures. rewrite bool_decide_decide E. wp_pures.

  awp_apply segment_next_spec. iApply (aacc_aupd_abort with "AU"); first done.
  iIntros "HInfArr".
  iDestruct (is_segment_by_location with "HHeadLoc HInfArr")
    as (? ?) "[HIsSeg HArrRestore]".
  iAaccIntro with "HIsSeg".
  { iIntros "HIsSeg !>". iDestruct ("HArrRestore" with "HIsSeg") as "$".
    by eauto with iFrame. }
  iIntros (?) "[HIsSeg #HNextLoc] !>".
  iDestruct (bi.later_wand with "HArrRestore HIsSeg") as "$".
  iIntros "AU !>".

  iAssert (□ ∀ v, ▷ is_valid_next γ id v -∗
    AU << ▷ is_infinite_array γ >> @ ⊤, ∅
       << ∃ (id': nat) (ℓ': loc), ▷ is_infinite_array γ ∗
          segment_location γ id' ℓ' ∗
          ((⌜fid <= id⌝ ∧ ⌜id = id'⌝) ∨
            ⌜id <= fid⌝ ∧ ⌜fid <= id'⌝ ∗
            [∗ list] i ∈ seq fid (id' - fid), segment_is_cancelled γ i),
          COMM Φ #ℓ' >> -∗
      WP ((find_segment segment_size) (from_some v)) #fid {{ v, Φ v }})%I as "#IH'".
  {
    iModIntro.
    iIntros (v) "#HValidNext AU".
    iDestruct "HValidNext" as (nnid ?) "(>% & >-> & >#SegLoc & #HSegCanc)".
    rewrite /from_some. wp_pures.
    iApply ("IH" with "[AU]").
    2: done.
    iAuIntro. iApply (aacc_aupd_commit with "AU"); first done.
    iIntros "HInfArr". iAaccIntro with "HInfArr".
    by iIntros "$ !> $ !>".
    iIntros (? ?) "[$ [#HRetSegLoc HH]] !>". iExists _, _; iSplit.
    2: by eauto. iFrame "HRetSegLoc". iRight.
    iSplitR; first by iPureIntro; lia.
    iDestruct "HH" as "[(% & <-)|(% & % & #HCanc')]".
    2: by eauto.
    iSplit; try done.
    repeat rewrite big_sepL_forall.
    iIntros (k ? HLt).
    apply seq_lookup' in HLt. inversion HLt; subst.
    iApply ("HSegCanc" $! (fid + k - S id)%nat).
    iPureIntro.
    replace (Some (fid + k)%nat) with (Some (S id + ((fid + k - S id))))%nat.
    2: by congr Some; lia.
    apply seq_lookup.
    lia.
  }

  awp_apply segment_next_read_spec; first done.
  iApply (aacc_aupd_abort with "AU"); first done.
  iIntros "HInfArr".
  iDestruct (segment_by_location with "HHeadLoc HInfArr")
    as "[[HNormSeg HArrRestore]|[HTailSeg HArrRestore]]".
  {
    iDestruct "HNormSeg" as (? ?) "[HIsSeg #HValidNext]".
    iAaccIntro with "HIsSeg"; iIntros "HIsSeg !>".
    { iSplitL.
      - iModIntro. iApply "HArrRestore". iExists _, _.
        iFrame "HIsSeg HValidNext".
      - eauto with iFrame. }
    iSplitL. iApply "HArrRestore"; iExists _, _; by iFrame.
    iIntros "AU !>".
    iDestruct "HValidNext" as (nnid ?) "(>% & >-> & >#SegLoc & #HSegCanc)".
    wp_alloc nextℓ as "Hnextℓ". wp_pures. wp_load.
    wp_pures. wp_load.
    iApply ("IH'" with "[] AU").
    rewrite /is_valid_next.
    iExists nnid, _. iFrame "SegLoc HSegCanc". eauto with iFrame.
  }

  iDestruct "HTailSeg" as (?) "HIsSeg".
  iAaccIntro with "HIsSeg"; iIntros "HIsSeg !>".
  { iSplitL.
    - iModIntro. iApply "HArrRestore". iExists _.
      iFrame "HIsSeg HValidNext".
    - eauto with iFrame. }
  iSplitL. iApply "HArrRestore"; iExists _; by iFrame.
  iIntros "AU !>".

  wp_alloc nextℓ as "Hnextℓ". wp_pures. wp_load. wp_pures.

  awp_apply segment_id_spec. iApply (aacc_aupd_abort with "AU"); first done.
  iIntros "HInfArr".
  iDestruct (is_segment_by_location with "HHeadLoc HInfArr")
    as (? ?) "[HIsSeg HArrRestore]".
  iAaccIntro with "HIsSeg".
  { iIntros "HIsSeg !>". iDestruct ("HArrRestore" with "HIsSeg") as "$".
    by eauto with iFrame. }
  iIntros "HIsSeg !>".
  iDestruct (bi.later_wand with "HArrRestore HIsSeg") as "$".
  iIntros "AU !>".

  rewrite /new_segment. wp_pures.
  wp_alloc nℓ as "Hnℓ". wp_alloc pℓ as "Hpℓ". wp_alloc dℓ as "Hdℓ". lia.
  wp_alloc cℓ as "Hcℓ". wp_alloc tℓ as "Hℓ". wp_pures.

  awp_apply segment_next_spec. iApply (aacc_aupd_abort with "AU"); first done.
  iIntros "HInfArr".
  iDestruct (is_segment_by_location with "HHeadLoc HInfArr")
    as (? ?) "[HIsSeg HArrRestore]".
  iAaccIntro with "HIsSeg".
  { iIntros "HIsSeg !>". iDestruct ("HArrRestore" with "HIsSeg") as "$".
    by eauto with iFrame. }
  iIntros (?) "[HIsSeg #HNextLoc'] !>".
  iDestruct (bi.later_wand with "HArrRestore HIsSeg") as "$".
  iIntros "AU !>".

  iDestruct (segment_next_location_agree with "HNextLoc' HNextLoc") as %->.
  iClear "HNextLoc'".
  wp_bind (CmpXchg _ _ _).

  iMod "AU" as "[HInfArr [HClose _]]".
  iDestruct (try_swap_tail with "HHeadLoc HInfArr")
    as "[[HNormSeg HArrRestore]|[HTailSeg HArrRestore]]".
  {
    iDestruct "HNormSeg" as (? ?) "[HIsSeg #HValidNext]".
    iDestruct "HIsSeg" as (? ? ? nnℓ ?) "(HIsSeg' & >HSegLocs & HIsSegCanc)".
    iAssert (segment_next_location γ id nnℓ) as "#HNextLoc'"; first by eauto 6.
    iDestruct (segment_next_location_agree with "HNextLoc' HNextLoc") as %->.
    iClear "HNextLoc'".
    iDestruct "HIsSeg'" as "(((HMem'' & HMem) & HMem') & HIsSegCells)".

    iDestruct (can_not_be_tail_if_has_next with "HValidNext") as "HNotTail".

    iDestruct "HValidNext" as (? ?) "(>% & >-> & HValidNext')".

    wp_cmpxchg_fail.

    iMod ("HClose" with "[HMem'' HMem HMem' HIsSegCells
                          HSegLocs HIsSegCanc HArrRestore]") as "AU".
    {
      iApply "HArrRestore". rewrite /is_normal_segment. iExists _, _.
      iSplitL.
      rewrite /is_segment /is_segment'; by eauto 20 with iFrame.
      rewrite /is_valid_next; by eauto 20 with iFrame.
    }

    iModIntro. wp_pures.

    awp_apply segment_next_spec. iApply (aacc_aupd_abort with "AU"); first done.
    iIntros "HInfArr".
    iDestruct (is_segment_by_location with "HHeadLoc HInfArr")
      as (? ?) "[HIsSeg HArrRestore]".
    iAaccIntro with "HIsSeg".
    { iIntros "HIsSeg !>". iDestruct ("HArrRestore" with "HIsSeg") as "$".
      by eauto with iFrame. }
    iIntros (?) "[HIsSeg #HNextLoc'] !>".
    iDestruct (bi.later_wand with "HArrRestore HIsSeg") as "$".
    iIntros "AU !>".

    iDestruct (segment_next_location_agree with "HNextLoc' HNextLoc") as %->.
    iClear "HNextLoc'".

    iClear "Hnℓ Hpℓ Hdℓ Hcℓ Hℓ".

    awp_apply segment_next_read_spec without "Hnextℓ"; first done.
    iApply (aacc_aupd_abort with "AU"); first done.
    iIntros "HInfArr".
    iDestruct (normal_segment_by_location with "HHeadLoc HNotTail HInfArr")
      as "[HNormSeg HArrRestore]".
    iDestruct "HNormSeg" as (? ?) "[HIsSeg #HValidNext]".
    iAaccIntro with "HIsSeg"; iIntros "HIsSeg !>".
    { iSplitL.
      - iModIntro. iApply "HArrRestore". iExists _, _.
        iFrame "HIsSeg HValidNext".
      - eauto with iFrame. }
    iSplitL. iApply "HArrRestore"; iExists _, _; by iFrame.
    iIntros "AU !>".

    iIntros "Hnextℓ".
    iDestruct "HValidNext" as (? ?) "(>% & >-> & HValidNext'')".
    wp_store. wp_load. wp_pures.

    iApply ("IH'" with "[] AU").
    rewrite /is_valid_next.
    iExists _, _. iFrame "HValidNext''". eauto with iFrame.
  }

  iDestruct "HTailSeg" as (?) "HIsSeg".
  iDestruct "HIsSeg" as (? ? ? nnℓ ?) "(HIsSeg' & >HSegLocs & HIsSegCanc)".
  iAssert (segment_next_location γ id nnℓ) as "#HNextLoc'"; first by eauto 6.
  iDestruct (segment_next_location_agree with "HNextLoc' HNextLoc") as %->.
  iClear "HNextLoc'".
  iDestruct "HIsSeg'" as "(((HMem'' & HMem) & HMem') & HIsSegCells)".

  wp_cmpxchg_suc.
  iDestruct "HArrRestore" as (segments' HLt) "(HAuth & HArrRestore)".

  replace (#(1%nat + id)) with (#(length segments')).
  2: rewrite -HLt; congr LitV; congr LitInt; lia.

  iDestruct (alloc_tail with "[HAuth Hnℓ Hpℓ Hcℓ Hdℓ Hℓ]") as ">HTail".
  { iFrame "HAuth Hnℓ Hpℓ Hcℓ Hdℓ Hℓ HCellInit". iRight.
    iExists _, _. iFrame "HHeadLoc".
    repeat iSplit; try (iPureIntro; try done; lia).
    rewrite HLt -minus_n_n /=. done. }

  iDestruct "HTail" as (?) "(HAuth & #HNewTailSegLoc & HIsTail)".

  iAssert (is_valid_next γ id (SOMEV #tℓ)) as "#HValidTrueNext".
  {
    rewrite /is_valid_next. iExists (length segments'), _.
    iSplit; first by iPureIntro; lia.
    iSplit; first by eauto.
    rewrite HLt -minus_n_n /=. by eauto with iFrame.
  }

  iMod ("HClose" with "[HMem HMem' HMem'' HIsSegCells HIsTail HAuth
                        HSegLocs HIsSegCanc HArrRestore]") as "AU".
  {
    rewrite HLt.
    iApply ("HArrRestore" with "[-HIsTail HAuth] HIsTail HAuth").
    iExists _, _. iSplitL. rewrite /is_segment /is_segment'.
    iExists _, _, _, _, _. iFrame "HIsSegCanc HSegLocs". by iFrame.
    done.
  }

  iModIntro. wp_pures.

  awp_apply segment_is_removed_spec without "Hnextℓ".
  iApply (aacc_aupd_abort with "AU"); first done.
  iIntros "HInfArr".
  iDestruct (is_segment_by_location with "HHeadLoc HInfArr")
    as (? ?) "[HIsSeg HArrRestore]".
  iAaccIntro with "HIsSeg".
  { iIntros "HIsSeg !>"; iDestruct ("HArrRestore" with "HIsSeg") as "$".
    by eauto with iFrame. }
  iIntros (is_removed) "(HIsSeg & #HCanc)".
  iDestruct (bi.later_wand with "HArrRestore HIsSeg") as "$".
  iIntros "!> AU !> Hnextℓ".

  iDestruct "HCanc" as "[->|[-> #HSegCanc]]"; wp_pures.

  1: wp_store; wp_load; iApply ("IH'" with "[$] AU").

  awp_apply remove_segment_spec without "Hnextℓ"; try done.
  iApply (aacc_aupd_abort with "AU"); first done.
  iIntros "HInfArr".
  iAaccIntro with "HInfArr".
  iIntros "$"; by eauto.
  iIntros (?) "[$ _] !> AU !> Hnextℓ".
  wp_pures.

  1: wp_store; wp_load; iApply ("IH'" with "[$] AU").

Qed.

End proof.
