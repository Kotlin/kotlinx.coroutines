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
  λ: "seg", ! segment_cancelled "seg" = #(Zpos segment_size).

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

Definition segment_remove : val :=
  λ: "seg", let: "next" := ref !(segment_next "seg") in
            let: "prev" := ref !(segment_prev "seg") in
            if: "next" = NONEV
              then NONE else
            (rec: "loop" <>:=
              if: "prev" = NONEV
                then #() else
              segment_move_next_to_right "prev" "next" ;;
              if: segment_is_removed "prev"
                then #() else
              "prev" <- segment_prev "prev" ;;
              "loop" #()
            ) #() ;;
            segment_move_prev_to_left "next" "prev" ;;
            (rec: "loop" <>:=
                if: (segment_is_removed "next" = #false) ||
                    !(segment_next "next") = NONE
                then #() else
                "next" <- segment_next "next" ;;
                segment_move_prev_to_left "next" "prev" ;;
                "loop" #()
            ) #() ;;
            SOME ("prev", "next").

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
  λ: <>, let: "initialSegment" := new_segment #0 NONE in
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
  rec: "loop" "arr" "cur" "fid" :=
    if: "fid" ≤ segment_id "cur" then "cur" else
      let: "next" := ref !(segment_next "cur") in
      (if: "next" = NONE then
         let: "newTail" := new_segment (#1 + segment_id "cur") "cur" in
         if: CAS (segment_next "cur") NONE "newTail" then
           move_tail_forward "arr" "newTail" ;;
           if: segment_is_removed "cur" then segment_remove "cur" else #()
         else
           "next" <- !(segment_next "cur")
       else
         "next" <- !(segment_next "cur")) ;;
      "loop" "arr" "next" "fid".

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
Variable cell_invariant: nat -> loc -> iProp.
Variable cell_invariant_persistent: forall ℓ n, Persistent (cell_invariant n ℓ).

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
  listUR segment_algebra := replicate id (ε, nil) ++ [s].

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
  rewrite pair_op.
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

End cancellation.

Definition is_valid_prev γ (id: nat) (pl: val): iProp :=
  (⌜pl = NONEV⌝ ∧
   ([∗ list] j ∈ seq 0 (id * Pos.to_nat segment_size),
    cell_is_cancelled γ j ∨ cell_is_done j) ∨
   ∃ (pid: nat) (prevℓ: loc),
     ⌜pid < id⌝ ∧ ⌜pl = SOMEV #prevℓ⌝ ∧
     segment_location γ pid prevℓ ∗
     [∗ list] j ∈ seq (S pid) id, segment_is_cancelled γ j)%I.

Global Instance is_valid_prev_persistent γ id pl:
  Persistent (is_valid_prev γ id pl).
Proof. apply _. Qed.

Definition is_valid_next γ (id: nat) (nl: val): iProp :=
  (∃ (nid: nat) (nextℓ: loc),
      ⌜id < nid⌝ ∧ ⌜nl = SOMEV #nextℓ⌝ ∧
      segment_location γ nid nextℓ ∗
      [∗ list] j ∈ seq (S id) nid, segment_is_cancelled γ j)%I.

Global Instance is_valid_next_persistent γ id pl:
  Persistent (is_valid_prev γ id pl).
Proof. apply _. Qed.

Definition is_segment' γ (id cancelled: nat) (ℓ dℓ cℓ pℓ nℓ: loc)
           (pl nl: val): iProp :=
  (((pℓ ↦ pl ∗ nℓ ↦ nl)
      ∗ ℓ ↦ (((#id, #cℓ), #dℓ), (#pℓ, #nℓ))
      ∗ cℓ ↦ #cancelled)
     ∗ ([∗ list] i ∈ seq 0 (Pos.to_nat segment_size),
        cell_invariant (id*Pos.to_nat segment_size+i)%nat
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
  (∃ pl nl, is_segment γ id ℓ pl nl ∗ is_valid_next γ id nl ∗
                       can_not_be_tail γ id)%I.

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
  <<< ∀ pl nl, ▷ is_segment γ id ℓ pl nl ∗ segment_prev_location γ id pℓ >>>
    ! #pℓ @ ⊤
  <<< is_segment γ id ℓ pl nl ∗ is_valid_prev γ id pl, RET pl >>>.
Proof.
  iIntros (Φ) "AU". iMod "AU" as (pl nl) "[[HIsSeg #HIsPrevLoc] [_ HClose]]".
  rename pℓ into pℓ'. iDestructHIsSeg.
  iAssert (segment_prev_location γ id pℓ) as "#HPrevLoc"; first by eauto 6.
  iDestruct (segment_prev_location_agree with "HIsPrevLoc HPrevLoc") as %->.
  wp_load.
  iCloseHIsSeg.
  iModIntro.
  by wp_pures.
Qed.

Theorem segment_prev_write_spec γ id (ℓ pℓ: loc) (pl: val):
  <<< ∀ pl' nl,
      ▷ is_segment γ id ℓ pl' nl ∗
                 segment_prev_location γ id pℓ ∗
                 is_valid_prev γ id pl
  >>>
  #pℓ <- pl @ ⊤
  <<< is_segment γ id ℓ pl nl, RET #() >>>.
Proof.
  iIntros (Φ) "AU".
  iMod "AU" as (pl' nl) "[[HIsSeg [#HIsPrevLoc #HIsValidPrev]] [_ HClose]]".
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
  <<< ∀ pl nl, ▷ is_segment γ id ℓ pl nl ∗ segment_next_location γ id nℓ >>>
    ! #nℓ @ ⊤
  <<< is_segment γ id ℓ pl nl, RET nl >>>.
Proof.
  iIntros (Φ) "AU". iMod "AU" as (pl nl) "[[HIsSeg #HIsNextLoc] [_ HClose]]".
  rename nℓ into nℓ'. iDestructHIsSeg.
  iAssert (segment_next_location γ id nℓ) as "#HNextLoc"; first by eauto 6.
  iDestruct (segment_next_location_agree with "HIsNextLoc HNextLoc") as %->.
  wp_load.
  iCloseHIsSeg.
  iModIntro.
  by wp_pures.
Qed.

Theorem segment_next_write_spec γ id (ℓ nℓ: loc) (nl: val):
  <<< ∀ pl nl', ▷ is_segment γ id ℓ pl nl' ∗ segment_next_location γ id nℓ >>>
    #nℓ <- nl @ ⊤
  <<< is_segment γ id ℓ pl nl, RET #() >>>.
Proof.
  iIntros (Φ) "AU". iMod "AU" as (pl nl') "[[HIsSeg #HIsNextLoc] [_ HClose]]".
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
  <<< ∀ pl nl, ▷ is_segment γ id ℓ pl nl ∗ segment_canc_location γ id cℓ >>>
    ! #cℓ @ ⊤
  <<< ∃ (cancelled: nat), is_segment γ id ℓ pl nl ∗
      (∃ cells,
          cells_are_cancelled γ id cells
          ∗ ⌜cancelled = length (List.filter (fun i => i) (vec_to_list cells))⌝),
      RET #cancelled >>>.
Proof.
  iIntros (Φ) "AU". iMod "AU" as (pl nl) "[[HIsSeg #HIsCancLoc] [_ HClose]]".
  rename cℓ into cℓ'. iDestructHIsSeg.
  iAssert (segment_canc_location γ id cℓ) as "#HCancLoc"; first by eauto 6.
  iDestruct (segment_canc_location_agree with "HIsCancLoc HCancLoc") as %->.
  wp_load.
  iCloseHIsSeg.
  iModIntro.
  by wp_pures.
Qed.

Theorem list_lookup_local_update {A: ucmraT}:
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

Theorem list_append_local_update {A: ucmraT}:
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

Theorem list_alter_local_update {A: ucmraT}:
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

Theorem segment_canc_incr_spec γ id cid (ℓ cℓ: loc) segments:
  (cid < Pos.to_nat segment_size)%nat ->
  <<< ∀ pl nl, ▷ is_segment γ id ℓ pl nl ∗ segment_canc_location γ id cℓ ∗
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
  iIntros (HCid Φ) "AU".
  iMod "AU" as (pl nl) "[[HIsSeg [#HIsCancLoc [HCancHandle HAuth]]] [_ HClose]]".
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
  rewrite -ias_cell_info'_op -Some_op Cinr_op.
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
                             ∗ cell_invariant
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
    iAssert (cell_invariant (id * Pos.to_nat segment_size + ix)%nat
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
  {{{ (ℓ dℓ cℓ pℓ nℓ: loc) nl, RET #ℓ;
      ([∗ list] i ∈ seq O (Pos.to_nat segment_size),
       ((dℓ +ₗ Z.of_nat i) ↦ InjLV #())
         -∗ cell_invariant (id * Pos.to_nat segment_size + i)%nat (dℓ +ₗ i)) -∗
      is_segment' γ id O ℓ dℓ cℓ pℓ nℓ pl nl }}}.
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

Definition is_segment_queue_inv γ tl : iProp :=
  (is_infinite_array γ ∗ ∃ id ℓ,
        ([∗ list] j ∈ seq 0 (id * Pos.to_nat segment_size),
         cell_is_processed j) ∗
        segment_location γ id ℓ ∗ tl ↦ #ℓ)%I.

Definition is_segment_queue γ v: iProp :=
  (∃ (tl: loc), ⌜v = #tl⌝ ∗ inv N (is_segment_queue_inv γ tl))%I.

Theorem is_segment_queue_persistent γ v: Persistent (is_segment_queue γ v).
Proof. apply _. Qed.

Lemma segment_by_location γ id ℓ:
  is_infinite_array γ -∗ segment_location γ id ℓ -∗
  ((is_normal_segment γ ℓ id ∗ (is_normal_segment γ ℓ id -∗ is_infinite_array γ)) ∨
   (is_tail_segment γ ℓ id ∗ (is_tail_segment γ ℓ id -∗ is_infinite_array γ))).
Proof.
  iIntros "HInfArr #HSegLoc".
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
  is_infinite_array γ -∗ segment_location γ id ℓ -∗
  ∃ nl, (∃ pl, is_segment γ id ℓ pl nl) ∗
                      (∀ pl, is_segment γ id ℓ pl nl -∗ is_infinite_array γ).
Proof.
  iIntros "HInfArr #HSegLoc".
  iDestruct (segment_by_location with "HInfArr HSegLoc")
    as "[[HNorm HRest]|[HTail HRest]]".
  1: iDestruct "HNorm" as (pl nl) "[HIsSeg #HValNext]".
  2: iDestruct "HTail" as (pl) "HIsSeg".
  all: iExists _; iSplitL "HIsSeg"; try by eauto 10.
  all: iIntros (?) "HSeg"; rewrite /is_segment_queue_inv; iApply "HRest".
  { rewrite /is_normal_segment. eauto 10 with iFrame. }
  { rewrite /is_tail_segment. eauto 10 with iFrame. }
Qed.

Lemma is_segment_by_location γ id ℓ:
  is_infinite_array γ -∗ segment_location γ id ℓ -∗
  ∃ pl nl, is_segment γ id ℓ pl nl ∗
                      (is_segment γ id ℓ pl nl -∗ is_infinite_array γ).
Proof.
  iIntros "HInfArr #HSegLoc".
  iDestruct (is_segment_by_location_prev with "HInfArr HSegLoc")
    as (nl) "[HIsSeg HArrRestore]".
  iDestruct "HIsSeg" as (pl) "HIsSeg".
  iExists _, _; iFrame. iApply "HArrRestore".
Qed.

Theorem move_tail_forward_spec γ v id ℓ:
  {{{ is_segment_queue γ v ∗ segment_location γ id ℓ ∗
      [∗ list] j ∈ seq 0 (id * Pos.to_nat segment_size), cell_is_processed j
  }}}
    move_tail_forward v #ℓ
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "[#HIsSegQ [#HSegLoc #HProc]] HPost". rewrite /is_segment_queue.
  iDestruct "HIsSegQ" as (tl) "[% HSeqInv]"; subst. wp_lam.
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
  iDestruct (bi.later_mono _ _ (is_segment_by_location γ id' ℓ')) as "HSeg".
  rewrite bi.later_wand.
  iDestruct ("HSeg" with "HIsInf HLoc") as (? ?) "[HIsSeg HArrRestore]".
  iAaccIntro with "HIsSeg"; iFrame; iIntros "HIsSeg"; iModIntro.
  1: by iApply "HArrRestore".
  iSplitL. by iApply "HArrRestore".
  iIntros "HPost". iClear "HSeg".
  awp_apply segment_id_spec without "HPost". iInv N as "[HIsInf Htl]".
  iDestruct (bi.later_mono _ _ (is_segment_by_location γ id ℓ)) as "HSeg".
  rewrite bi.later_wand.
  iDestruct ("HSeg" with "HIsInf HSegLoc") as (? ?) "[HIsSeg HArrRestore]".
  iAaccIntro with "HIsSeg"; iFrame; iIntros "HIsSeg"; iModIntro.
  1: by iApply "HArrRestore".
  iSplitL. by iApply "HArrRestore".
  iIntros "HPost". iClear "HSeg".
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

Theorem segment_move_next_to_right_spec γ id (ℓ: loc) mnl:
  is_valid_next γ id mnl -∗
  <<< ▷ is_normal_segment γ ℓ id ∗ ▷ is_infinite_array γ >>>
    segment_move_next_to_right #ℓ mnl @ ⊤
  <<< ▷ is_normal_segment γ ℓ id ∗ ▷ is_infinite_array γ, RET #() >>>.
Proof.
  iIntros "#HValidNewNext". iIntros (Φ) "AU". wp_lam.
  rewrite /from_some. wp_pures.
  iLöb as "IH".
  awp_apply segment_next_spec.
  iApply (aacc_aupd_abort with "AU"); first done.
  iIntros "[HSeg HInfArr]". iDestruct "HSeg" as (pl nl) "[HIsSeg >#HValidNext]".
  iAaccIntro with "HIsSeg"; iFrame.
  { rewrite /is_normal_segment. iIntros "HIsSeg".
    iModIntro. iSplitL; eauto with iFrame. }
  iIntros (nℓ) "[HIsSeg #HNextLoc] !>".
  iSplitL. { rewrite /is_normal_segment. eauto with iFrame. }
  iIntros "AU !>".
  awp_apply segment_next_read_spec.
  iApply (aacc_aupd_abort with "AU"); first done.
  iIntros "[HIsSeg HInfArr]".
  iDestruct "HIsSeg" as (pl' nl') "[HIsSeg >#[HValidNext' #HNotTail']]".
  iCombine "HIsSeg" "HNextLoc" as "HEv".
  iAaccIntro with "HEv"; iFrame.
  { iIntros "[HIsSeg _] !>". rewrite /is_normal_segment.
    iSplitL; eauto 6 with iFrame. }
  iIntros "HIsSeg !>". iSplitL.
  { rewrite /is_normal_segment. eauto 6 with iFrame. }
  iIntros "AU !>". wp_pures.
  iDestruct "HValidNext'" as (nid nextℓ)
                              "(% & -> & #HNextSegLoc & HCanc)".
  iDestruct "HValidNewNext" as (mnid mnextℓ)
                              "(% & -> & #HMNextSegLoc & HMCanc)".
  wp_pures.
  awp_apply segment_id_spec.
  iApply (aacc_aupd_abort with "AU"); first done.
  iIntros "[HIsSeg HInfArr]".
  iDestruct (is_segment_by_location with "HInfArr") as "HLoc".
  iDestruct (bi.later_wand with "HLoc HNextSegLoc")
    as (pl'' nl'') "[HIsSeg' HArrRestore]".
  iAaccIntro with "HIsSeg'"; iFrame.
  { iIntros "HIsSeg". iSpecialize ("HArrRestore" with "HIsSeg").
    eauto with iFrame. }
  iIntros "HIsSeg !>". iSplitL. by iApply "HArrRestore".
  iIntros "AU !>".
  awp_apply segment_id_spec.
  iApply (aacc_aupd_abort with "AU"); first done.
  iIntros "[HIsSeg HInfArr]".
  iDestruct (is_segment_by_location with "HInfArr") as "HLoc".
  iDestruct (bi.later_wand with "HLoc HMNextSegLoc")
    as (pl''' nl''') "[HIsSeg' HArrRestore]".
  iAaccIntro with "HIsSeg'"; iFrame.
  { iIntros "HIsSeg". iSpecialize ("HArrRestore" with "HIsSeg").
    eauto with iFrame. }
  iIntros "HIsSeg !>". iSplitL. by iApply "HArrRestore".
  iIntros "AU".
  destruct (bool_decide (mnid <= nid)) eqn:E.
  { iMod "AU" as "[[HSeg HInfArr] [_ HClose]]".
    iMod ("HClose" with "[HSeg HInfArr]") as "HΦ".
      by iFrame.
    iModIntro. wp_pures. rewrite E. by wp_pures. }
  iModIntro. wp_pures. rewrite E. wp_pures.
  awp_apply segment_next_spec.
  iApply (aacc_aupd_abort with "AU"); first done.
  iIntros "[HSeg HInfArr]".
  iDestruct "HSeg" as (plx nlx) "[HIsSeg >#HValidNext']".
  iAaccIntro with "HIsSeg"; iFrame.
  { rewrite /is_normal_segment. iIntros "HIsSeg".
    iModIntro. iSplitL; eauto with iFrame. }
  iIntros (nℓ') "[HIsSeg #HNextLoc'] !>".
  iSplitL. { rewrite /is_normal_segment. eauto with iFrame. }
  iIntros "AU !>". wp_bind (CmpXchg _ _ _).
  iDestruct (segment_next_location_agree with "HNextLoc' HNextLoc") as %->.
  iMod "AU" as "[[HSeg HInfArr] HClose]".
  iDestruct "HSeg" as (ply nly) "[HIsSeg >#HValidNext'']".
  rewrite /is_segment.
  iDestruct "HIsSeg"
    as (dℓ cℓ pℓ nℓ' cancelled_locs) "(HIsSeg' & >#HLocs & HCancS)".
  iAssert (segment_next_location γ id nℓ') as "#HNextLoc''";
    first by eauto 6 with iFrame.
  iDestruct (segment_next_location_agree with "HNextLoc'' HNextLoc'") as %->.
  iClear "HNextLoc' HNextLoc''".
  iDestruct "HIsSeg'" as "([[HMem'' Hnl] HMem'] & HCells)".
  destruct (decide (nly = InjRV #nextℓ)); subst.
  {
    wp_cmpxchg_suc. iDestruct "HClose" as "[_ HClose]".
    iMod ("HClose" with "[-]") as "HΦ".
    2: by iModIntro; wp_pures.
    iFrame. rewrite /is_normal_segment /is_segment /is_segment'.
    iExists ply, (InjRV #mnextℓ).
    iSplitL. iExists dℓ, cℓ, pℓ, nℓ, cancelled_locs.
    by eauto 10 with iFrame.
    rewrite /is_valid_next. eauto 10 with iFrame.
  }
  {
    wp_cmpxchg_fail. iDestruct "HClose" as "[HClose _]".
    iMod ("HClose" with "[-]") as "AU".
    { rewrite /is_normal_segment /is_segment /is_segment'.
      by eauto 20 with iFrame. }
    iModIntro. wp_pures. wp_lam. wp_pures.
    iApply "IH". done.
  }
Qed.

Theorem segment_move_prev_to_left_spec γ id (ℓ: loc) mpl:
  is_valid_prev γ id mpl -∗
  <<< ∀ pl nl, ▷ is_segment γ id ℓ pl nl ∗ ▷ is_infinite_array γ >>>
    segment_move_prev_to_left #ℓ mpl @ ⊤
  <<< ∃ pl', ▷ is_segment γ id ℓ pl' nl ∗ ▷ is_infinite_array γ, RET #() >>>.
Proof.
  iIntros "#HNewValidPrev". iIntros (Φ) "AU". wp_lam. wp_pures.
  rewrite /from_some. iLöb as "IH".
  awp_apply segment_prev_spec; iApply (aacc_aupd_abort with "AU"); first done.
  iIntros (? ?) "[HSeg HInfArr]". iAaccIntro with "HSeg"; iFrame.
  1: by eauto 10 with iFrame.
  iIntros (?) "[$ #HPrevLoc] !> AU !>".
  awp_apply segment_prev_read_spec. iApply (aacc_aupd with "AU"); first done.
  iIntros (? ?) "[HSeg HInfArr]". iCombine "HSeg" "HPrevLoc" as "HEv".
  iAaccIntro with "HEv"; iFrame. { iIntros "[HIsSeg _]". eauto 10 with iFrame. }
  iIntros "[HIsSeg #HValidPrev] !>".
  iDestruct "HValidPrev" as "[[-> HCanc]|#HValidPrev']".
  { iRight. iExists _. iFrame. iIntros "HΦ !>". by wp_pures. }
  iDestruct "HValidPrev'" as (pid prevℓ) "(% & -> & #HPrevSegLoc & HNewCanc)".
  iLeft. iFrame. iIntros "AU !>". wp_pures.
  iDestruct "HNewValidPrev" as "[[-> HNewCanc']|#HNewValidPrev']".
  wp_pures.
  2: iDestruct "HNewValidPrev'"
    as (npid nprevℓ) "(% & -> & #HNPrevSegLoc & HNewCanc')".
  all: wp_pures.
  {
    awp_apply segment_prev_spec; iApply (aacc_aupd_abort with "AU"); first done.
    iIntros (? ?) "[HSeg HInfArr]". iAaccIntro with "HSeg"; iFrame.
    by eauto with iFrame. iIntros (pℓ') "[$ #HPrevLoc'] !> AU !>".
    iDestruct (segment_prev_location_agree with "HPrevLoc' HPrevLoc") as %->.
    iClear "HPrevLoc'".
    wp_bind (CmpXchg _ _ _). iMod "AU" as (pl nl) "[[HIsSeg HInfArr] HClose]".
    iDestructHIsSeg.
    iAssert (segment_prev_location γ id pℓ) as "#HPrevLoc'";
      first by eauto 6 with iFrame.
    iDestruct (segment_prev_location_agree with "HPrevLoc HPrevLoc'") as %->.
    iClear "HPrevLoc'".
    destruct (decide (pl = InjRV #prevℓ)); subst.
    { wp_cmpxchg_suc. iDestruct "HClose" as "[_ HClose]".
      iMod ("HClose" with "[-]") as "HΦ".
      2: by iModIntro; wp_pures.
      rewrite /is_segment /is_segment' /is_valid_prev.
      iFrame "HInfArr". iExists dℓ, cℓ, pℓ, nℓ, _.
      iSplitR "HCancParts". 2: iSplitR; eauto 10 with iFrame.
      eauto 10 with iFrame.
    }
    { wp_cmpxchg_fail. iDestruct "HClose" as "[HClose _]".
      iMod ("HClose" with "[-]") as "AU".
      { rewrite /is_segment /is_segment' /is_valid_prev.
        iFrame "HInfArr". iExists dℓ, cℓ, pℓ, nℓ, _.
        eauto 10 with iFrame. }
      iModIntro. wp_pures. wp_lam. wp_pures.
      by iApply "IH".
    }
  }
  {
    awp_apply segment_id_spec; iApply (aacc_aupd_abort with "AU"); first done.
    iIntros (? ?) "[HSeg HInfArr]".
    iDestruct (is_segment_by_location with "HInfArr") as "HLoc".
    iDestruct (bi.later_wand with "HLoc HNPrevSegLoc")
      as (? ?) "[HIsSeg HArrRestore]".
    iAaccIntro with "HIsSeg".
    { iIntros "HIsSeg". iSpecialize ("HArrRestore" with "HIsSeg").
      by eauto 10 with iFrame. }
    iIntros "HIsSeg !>". iSplitL.
    { iFrame. by iApply "HArrRestore". }
    iIntros "AU !>". wp_pures.

    awp_apply segment_id_spec; iApply (aacc_aupd with "AU"); first done.
    iIntros (? ?) "[HSeg HInfArr]".
    iDestruct (is_segment_by_location_prev with "HInfArr") as "HLoc".
    iDestruct (bi.later_wand with "HLoc HPrevSegLoc")
      as (?) "[HIsSeg HArrRestore]". iDestruct "HIsSeg" as (?) "HIsSeg".
    iAaccIntro with "HIsSeg".
    { iIntros "HIsSeg". iSpecialize ("HArrRestore" with "HIsSeg").
      by eauto 10 with iFrame. }
    iIntros "HIsSeg !>".
    rewrite bi.later_forall.
    iDestruct (bi.later_wand with "HArrRestore HIsSeg") as "HArr".

    destruct (bool_decide (pid <= npid)) eqn:E.
    { iRight. iExists _. iFrame.
      iIntros "HΦ !>". wp_pures. rewrite E. by wp_pures.
    }
    { iLeft. iFrame. iIntros "AU !>". wp_pures. rewrite E. wp_pures.

  (* Mostly copy-pasted from above. *)
  {
    awp_apply segment_prev_spec; iApply (aacc_aupd_abort with "AU"); first done.
    iIntros (? ?) "[HSeg HInfArr]". iAaccIntro with "HSeg"; iFrame.
    by eauto with iFrame. iIntros (pℓ') "[$ #HPrevLoc'] !> AU !>".
    iDestruct (segment_prev_location_agree with "HPrevLoc' HPrevLoc") as %->.
    iClear "HPrevLoc'".
    wp_bind (CmpXchg _ _ _). iMod "AU" as (pl nl) "[[HIsSeg HInfArr] HClose]".
    iDestructHIsSeg.
    iAssert (segment_prev_location γ id pℓ) as "#HPrevLoc'";
      first by eauto 6 with iFrame.
    iDestruct (segment_prev_location_agree with "HPrevLoc HPrevLoc'") as %->.
    iClear "HPrevLoc'".
    destruct (decide (pl = InjRV #prevℓ)); subst.
    { wp_cmpxchg_suc. iDestruct "HClose" as "[_ HClose]".
      iMod ("HClose" with "[-]") as "HΦ".
      2: by iModIntro; wp_pures.
      rewrite /is_segment /is_segment' /is_valid_prev.
      iFrame "HInfArr". iExists dℓ, cℓ, pℓ, nℓ, _.
      iSplitR "HCancParts". 2: iSplitR; eauto 10 with iFrame.
      iFrame. iSplit. 1: done. iRight. iClear "IH HValidPrev".
      iExists npid, _. eauto 10 with iFrame.
    }
    { wp_cmpxchg_fail. iDestruct "HClose" as "[HClose _]".
      iMod ("HClose" with "[-]") as "AU".
      { rewrite /is_segment /is_segment' /is_valid_prev.
        iFrame "HInfArr". iExists dℓ, cℓ, pℓ, nℓ, _.
        eauto 10 with iFrame. }
      iModIntro. wp_pures. wp_lam. wp_pures.
      by iApply "IH".
    }
  }
  }
    }
Qed.

Lemma normal_segment_by_location γ id ℓ:
  is_infinite_array γ -∗ segment_location γ id ℓ -∗ can_not_be_tail γ id -∗
  (is_normal_segment γ ℓ id ∗ (is_normal_segment γ ℓ id -∗ is_infinite_array γ)).
Proof.
  iIntros "HInfArr #HSegLoc #HNotTail".
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

Theorem find_segment_spec γ v (ℓ: loc) fid:
  {{{ is_segment_queue γ v ∗ segment_location γ fid ℓ ∗
      [∗ list] j ∈ seq 0 (fid * Pos.to_nat segment_size), cell_is_processed j
  }}}
    (find_segment segment_size) v #ℓ #fid
  {{{ ℓ', RET #ℓ'; True }}}.
Proof.
  iIntros (Φ) "[HIsSegQ [#HHeadLoc #HProc]] HPost". wp_lam.
  wp_pures. iLöb as "IH".
  wp_bind (segment_id #ℓ). rewrite /is_segment_queue.
  iDestruct "HIsSegQ" as (tl) "[-> #HInv]".
  awp_apply segment_id_spec without "HPost".
  iInv N as "[HIsInf Htl]".
  iDestruct (bi.later_mono _ _ (is_segment_by_location γ fid ℓ)) as "HSeg".
  iSpecialize ("HSeg" with "HIsInf").
  iDestruct (bi.later_wand with "HSeg") as "HSeg".
  iDestruct ("HSeg" with "HHeadLoc") as (? ?) "[HIsSeg HArrRestore]".
  iAaccIntro with "HIsSeg"; iIntros "HSeg"; iFrame.
  1: by iApply (bi.later_wand with "HArrRestore").
  iSplitL. by iApply (bi.later_wand with "HArrRestore").
  iModIntro. iIntros "HPost". wp_pures.
  destruct (bool_decide (fid <= fid)); try lia; wp_pures.
  1: by iApply "HPost".
  awp_apply segment_next_spec without "HPost". iInv N as "[HIsInf Htl]".
  iDestruct (bi.later_mono _ _ (is_segment_by_location γ fid ℓ)) as "HSeg".
  iSpecialize ("HSeg" with "HIsInf").
  iDestruct (bi.later_wand with "HSeg") as "HSeg".
Abort.

End proof.
