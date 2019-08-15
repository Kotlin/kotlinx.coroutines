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

Definition segment_move_next_to_right : val :=
  rec: "loop" "seg" "next" := let: "curNext" := segment_next "seg" in
                              if: segment_id "next" ≤ segment_id "curNext" ||
                                  CAS (segment_next "seg") "curNext" "next"
                              then #() else "loop" "seg" "next".

Definition segment_move_prev_to_left : val :=
  rec: "loop" "seg" "prev" := let: "curPrev" := segment_prev "seg" in
                              if: "curPrev" = NONE ||
                                  !("prev" = NONE) &&
                                  segment_id "curPrev" ≤ segment_id "prev" ||
                                  CAS (segment_next "seg") "curPrev" "prev"
                              then #() else "loop" "seg" "prev".

Definition segment_remove : val :=
  λ: "seg", let: "next" := ref !(segment_next "seg") in
            let: "prev" := ref !(segment_prev "seg") in
            if: "next" = NONEV
              then ("prev", "next") else
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
              if: !segment_is_removed "next" || !(segment_next "next") = NONE
                then #() else
                "next" <- segment_next "next" ;;
                segment_move_prev_to_left "next" "prev" ;;
                "loop" #()
            ) #() ;;
            ("prev", "next").

Definition segment_cutoff : val :=
  λ: "seg", (segment_prev "seg") <- NONE.

Definition segment_cancel_cell : val :=
  λ: "seg", FAA (segment_cancelled "seg") #-1.

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

Notation segment_cancellation_algebra :=(optionUR (csumR (agreeR unitO)
                                                         positiveR
                                        )).

Notation segment_locations_algebra :=
  (prodUR (prodUR (optionUR (agreeR locO))
                  (prodUR (optionUR (agreeR locO))
                          (optionUR (agreeR locO))))
          (prodUR (optionUR (agreeR locO))
                  (optionUR (agreeR locO)))).

Notation segment_algebra := (prodUR (prodUR segment_locations_algebra
                                            segment_cancellation_algebra
                                    )
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

Section array_mapsto.

Definition array_mapsto' γ ns nc ℓ: iProp :=
  ((∃ (dℓ: loc), ⌜ℓ = dℓ +ₗ Z.of_nat nc⌝ ∧
                 own γ (◯ (ias_segment_info
                             ns (((ε, (Some (to_agree dℓ), ε)), ε), ε, nil))))
  )%I.

Global Instance array_mapsto'_persistent γ ns nc ℓ:
  Persistent (array_mapsto' γ ns nc ℓ).
Proof.
  apply bi.exist_persistent; intros;
    apply bi.and_persistent; first by apply _.
  apply own_core_persistent; apply auth_frag_core_id;
    apply ias_segment_info_core_id.
  repeat apply pair_core_id; apply _.
Qed.

Definition array_mapsto γ (id: nat) (ℓ: loc): iProp :=
  ias_cell_info_view (fun ns nc => array_mapsto' γ ns nc ℓ) id.

Theorem array_mapsto'_agree γ (ns nc: nat) (ℓ ℓ': loc):
  array_mapsto' γ ns nc ℓ -∗ array_mapsto' γ ns nc ℓ' -∗ ⌜ℓ = ℓ'⌝.
Proof.
  rewrite /array_mapsto'.
  iIntros "Ham Ham'".
  iDestruct "Ham" as (dℓ) "[% Ham]".
  iDestruct "Ham'" as (dℓ') "[% Ham']".
  subst.
  iDestruct (own_valid_2 with "Ham Ham'") as %Hv.
  iPureIntro.
  revert Hv.
  rewrite auth_frag_valid list_lookup_valid -ias_segment_info_op.
  intros Hv.
  specialize (Hv ns).
  rewrite ias_segment_info_lookup in Hv.
  revert Hv. repeat case. simpl. intros.
  assert (dℓ = dℓ') as <- by (apply agree_op_invL'; assumption).
  done.
Qed.

Theorem array_mapsto_agree γ n (ℓ ℓ': loc):
  array_mapsto γ n ℓ -∗ array_mapsto γ n ℓ' -∗ ⌜ℓ = ℓ'⌝.
Proof. apply array_mapsto'_agree. Qed.

Global Instance array_mapsto_persistent γ ns nc ℓ: Persistent (array_mapsto' γ ns nc ℓ).
Proof. apply _. Qed.

End array_mapsto.

Section cancellation.

Definition segment_is_cancelled γ (n: nat): iProp :=
  own γ (◯ (ias_segment_info n (ε, Some (Cinl (to_agree tt)), nil))).

Global Instance segment_is_cancelled_persistent γ n:
  Persistent (segment_is_cancelled γ n).
Proof. by segment_info_persistent. Qed.

Definition cell_is_cancelled' γ (ns nc: nat): iProp :=
  own γ (◯ (ias_cell_info' ns nc (Some (Cinl (to_agree tt))))).
Definition cell_is_cancelled γ := ias_cell_info_view (cell_is_cancelled' γ).

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

Global Instance cell_is_cancelled_persistent γ n:
  Persistent (cell_is_cancelled γ n).
Proof. apply _. Qed.

End cancellation.

Section locations.

Definition segments_mapto γ (locs: list loc): iProp :=
  own γ (◯ ((fun ℓ => (Some (to_agree ℓ), ε, ε, ε, nil)) <$> locs)).

Global Instance segments_mapto_persistent γ locs:
  Persistent (segments_mapto γ locs).
Proof.
  apply own_core_persistent.
  apply auth_frag_core_id.
  apply list_core_id'.
  intros ? Hel.
  apply elem_of_map in Hel.
  destruct Hel as [? [_ Heq]].
  subst.
  repeat apply pair_core_id; apply _.
Qed.

Definition is_valid_prev γ (id: nat) (pl: val): iProp :=
  (⌜pl = NONEV⌝ ∧
   ([∗ list] j ∈ seq 0 (id * Pos.to_nat segment_size),
    cell_is_cancelled γ j ∨ cell_is_done j) ∨
   ∃ (segment_locs: list loc),
     segments_mapto γ segment_locs ∗
   ∃ (pid: nat),
     ⌜Some pl = option_map (LitV ∘ LitLoc) (segment_locs !! pid)⌝ ∧
     ⌜pid < id⌝ ∧
     [∗ list] j ∈ seq (S pid) id, segment_is_cancelled γ j)%I.

Global Instance is_valid_prev_persistent γ id pl:
  Persistent (is_valid_prev γ id pl).
Proof. apply _. Qed.

Definition is_valid_next γ (id: nat) (nl: val): iProp :=
  (∃ (segment_locs: list loc), segments_mapto γ segment_locs ∗
   ∃ (nid: nat),
      ⌜Some nl = option_map (fun x => LitV (LitLoc x)) (segment_locs !! nid)⌝ ∧
      ⌜id < nid⌝ ∧
      [∗ list] j ∈ seq (S id) nid, segment_is_cancelled γ j)%I.

Global Instance is_valid_next_persistent γ id pl:
  Persistent (is_valid_prev γ id pl).
Proof. apply _. Qed.

Definition segment_location γ id ℓ : iProp :=
  own γ (◯ (ias_segment_info id (Some (to_agree ℓ), ε, ε, ε, nil))).
Definition segment_data_location γ id dℓ: iProp :=
  own γ (◯ (ias_segment_info id (ε, (Some (to_agree dℓ), ε), ε, ε, nil))).
Definition segment_canc_location γ id cℓ: iProp :=
  own γ (◯ (ias_segment_info id (ε, (ε, Some (to_agree cℓ)), ε, ε, nil))).
Definition segment_prev_location γ id pℓ: iProp :=
  own γ (◯ (ias_segment_info id (ε, (Some (to_agree pℓ), ε), ε, nil))).
Definition segment_next_location γ id nℓ: iProp :=
  own γ (◯ (ias_segment_info id (ε, (ε, Some (to_agree nℓ)), ε, nil))).

Global Instance segment_location_persistent γ id ℓ:
  Persistent (segment_location γ id ℓ).
Proof. by segment_info_persistent. Qed.
Global Instance segment_data_location_persistent γ id dℓ:
  Persistent (segment_data_location γ id dℓ).
Proof. by segment_info_persistent. Qed.
Global Instance segment_canc_location_persistent γ id dℓ:
  Persistent (segment_canc_location γ id dℓ).
Proof. by segment_info_persistent. Qed.
Global Instance segment_prev_location_persistent γ id pℓ:
  Persistent (segment_prev_location γ id pℓ).
Proof. by segment_info_persistent. Qed.
Global Instance segment_next_location_persistent γ id nℓ:
  Persistent (segment_next_location γ id nℓ).
Proof. by segment_info_persistent. Qed.

Theorem segment_location_agree γ id ℓ ℓ':
  segment_location γ id ℓ -∗ segment_location γ id ℓ' -∗ ⌜ℓ = ℓ'⌝.
Proof. iIntros "HLoc1 HLoc2".
  iDestruct (own_valid_2 with "HLoc1 HLoc2") as %HValid; iPureIntro.
  revert HValid.
  rewrite auth_frag_valid -ias_segment_info_op ias_segment_info_valid.
  repeat case; simpl; intros.
  by apply agree_op_invL'.
Qed.

Theorem segment_data_location_agree γ id ℓ ℓ':
  segment_data_location γ id ℓ -∗ segment_data_location γ id ℓ' -∗ ⌜ℓ = ℓ'⌝.
Proof. iIntros "HLoc1 HLoc2".
  iDestruct (own_valid_2 with "HLoc1 HLoc2") as %HValid; iPureIntro.
  revert HValid.
  rewrite auth_frag_valid -ias_segment_info_op ias_segment_info_valid.
  repeat case; simpl; intros.
  by apply agree_op_invL'.
Qed.

Theorem segment_canc_location_agree γ id ℓ ℓ':
  segment_canc_location γ id ℓ -∗ segment_canc_location γ id ℓ' -∗ ⌜ℓ = ℓ'⌝.
Proof. iIntros "HLoc1 HLoc2".
  iDestruct (own_valid_2 with "HLoc1 HLoc2") as %HValid; iPureIntro.
  revert HValid.
  rewrite auth_frag_valid -ias_segment_info_op ias_segment_info_valid.
  repeat case; simpl; intros.
  by apply agree_op_invL'.
Qed.

Theorem segment_prev_location_agree γ id ℓ ℓ':
  segment_prev_location γ id ℓ -∗ segment_prev_location γ id ℓ' -∗ ⌜ℓ = ℓ'⌝.
Proof. iIntros "HLoc1 HLoc2".
  iDestruct (own_valid_2 with "HLoc1 HLoc2") as %HValid; iPureIntro.
  revert HValid.
  rewrite auth_frag_valid -ias_segment_info_op ias_segment_info_valid.
  repeat case; simpl; intros.
  by apply agree_op_invL'.
Qed.

Theorem segment_next_location_agree γ id ℓ ℓ':
  segment_next_location γ id ℓ -∗ segment_next_location γ id ℓ' -∗ ⌜ℓ = ℓ'⌝.
Proof. iIntros "HLoc1 HLoc2".
  iDestruct (own_valid_2 with "HLoc1 HLoc2") as %HValid; iPureIntro.
  revert HValid.
  rewrite auth_frag_valid -ias_segment_info_op ias_segment_info_valid.
  repeat case; simpl; intros.
  by apply agree_op_invL'.
Qed.

End locations.

Definition cancelled_cells γ id (cells: vec bool (Pos.to_nat segment_size)) :=
  (own γ (◯ (ias_segment_info
               id (ε,
                   map (fun (c: bool) =>
                          (if c then Some (Cinl (to_agree tt)) else None))
                       (vec_to_list cells)))))%I.

Global Instance cancelled_cells_persistent γ id cells:
  Persistent (cancelled_cells γ id cells).
Proof.
  segment_info_persistent.
  apply list_core_id'.
  intros x Hel. apply elem_of_map in Hel.
  destruct Hel as [y [_ He]]; subst. destruct y; apply _.
Qed.

Definition is_segment' γ (id cancelled: nat) (ℓ dℓ cℓ pℓ nℓ: loc)
           (pl nl: val): iProp :=
  (((pℓ ↦ pl ∗ nℓ ↦ nl)
      ∗ ℓ ↦ (((#id, #cℓ), #dℓ), (#pℓ, #nℓ))
      ∗ cℓ ↦ #cancelled)
     ∗ ([∗ list] i ∈ seq 0 (Pos.to_nat segment_size),
        cell_invariant (id*Pos.to_nat segment_size+i)%nat
                       (dℓ +ₗ Z.of_nat i))
     ∗ is_valid_prev γ id pl)%I.

Definition is_segment γ (id: nat) (ℓ: loc) (pl nl: val) : iProp :=
  (∃ dℓ cℓ pℓ nℓ cancelled,
      is_segment' γ id cancelled ℓ dℓ cℓ pℓ nℓ pl nl
                  ∗ ((segment_location γ id ℓ ∗ segment_data_location γ id dℓ
                       ∗ segment_canc_location γ id cℓ)
                       ∗ segment_prev_location γ id pℓ
                       ∗ segment_next_location γ id nℓ) ∗
      (∃ (cells: vec bool (Pos.to_nat segment_size)),
          ⌜cancelled = length (List.filter (fun i => i) (vec_to_list cells))⌝ ∗
          let uncancelled := (Pos.to_nat segment_size - cancelled)%nat in
          cancelled_cells γ id cells ∗
          own γ (◯ (ias_segment_info
                      id
                      (ε, ε,
                        Some (if Nat.eqb uncancelled O
                              then Cinl (to_agree tt)
                              else Cinr (Pos.of_nat uncancelled)),
                        map (fun (c: bool) =>
                              (Some (if c
                                      then Cinl (to_agree tt)
                                      else Cinr (1/4)%Qp)))
                            (vec_to_list cells)))))
  )%I.

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
  iDestruct "HIsSeg" as
    (dℓ cℓ pℓ nℓ cancelled)
      "[HIsSeg [[[#HLoc [#HDataLoc #HCancLoc]] [#HPrevLoc #HNextLoc]] HCanc]]";
  iDestruct "HIsSeg" as "[[[Hpℓ Hnℓ] [Hℓ Hcℓ]] [#HCells #HValidPrev]]".

Ltac iCloseHIsSeg := iMod ("HClose" with "[HCanc Hpℓ Hnℓ Hℓ Hcℓ]") as "HΦ";
  first by (rewrite /is_segment /is_segment'; eauto 20 with iFrame).

Theorem segment_id_spec γ id (ℓ: loc):
  <<< ∀ pl nl, is_segment γ id ℓ pl nl >>>
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
  <<< ∀ pl nl, is_segment γ id ℓ pl nl >>>
    segment_prev #ℓ @ ⊤
    <<< ∃ (pℓ: loc),
          is_segment γ id ℓ pl nl ∗ segment_prev_location γ id pℓ, RET #pℓ >>>.
Proof.
  iIntros (Φ) "AU". wp_lam.
  wp_bind (!_)%E. iMod "AU" as (pl nl) "[HIsSeg [_ HClose]]".
  iDestructHIsSeg.
  wp_load.
  iCloseHIsSeg.
  iModIntro.
  by wp_pures.
Qed.

Theorem segment_prev_read_spec γ id (ℓ pℓ: loc):
  <<< ∀ pl nl, is_segment γ id ℓ pl nl ∗ segment_prev_location γ id pℓ >>>
    ! #pℓ @ ⊤
  <<< is_segment γ id ℓ pl nl ∗ is_valid_prev γ id pl, RET pl >>>.
Proof.
  iIntros (Φ) "AU". iMod "AU" as (pl nl) "[[HIsSeg #HIsPrevLoc] [_ HClose]]".
  rename pℓ into pℓ'. iDestructHIsSeg.
  iDestruct (segment_prev_location_agree with "HIsPrevLoc HPrevLoc") as %->.
  wp_load.
  iCloseHIsSeg.
  iModIntro.
  by wp_pures.
Qed.

Theorem segment_prev_write_spec γ id (ℓ pℓ: loc) (pl: val):
  <<< ∀ pl' nl,
      is_segment γ id ℓ pl' nl ∗
                 segment_prev_location γ id pℓ ∗
                 is_valid_prev γ id pl
  >>>
  #pℓ <- pl @ ⊤
  <<< is_segment γ id ℓ pl nl, RET #() >>>.
Proof.
  iIntros (Φ) "AU".
  iMod "AU" as (pl' nl) "[[HIsSeg [#HIsPrevLoc #HIsValidPrev]] [_ HClose]]".
  rename pℓ into pℓ'. iDestructHIsSeg.
  iDestruct (segment_prev_location_agree with "HIsPrevLoc HPrevLoc") as %->.
  wp_store.
  iCloseHIsSeg.
  by iModIntro.
Qed.

Theorem segment_next_spec γ id (ℓ: loc):
  <<< ∀ pl nl, is_segment γ id ℓ pl nl >>>
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
  <<< ∀ pl nl, is_segment γ id ℓ pl nl ∗ segment_next_location γ id nℓ >>>
    ! #nℓ @ ⊤
  <<< is_segment γ id ℓ pl nl, RET nl >>>.
Proof.
  iIntros (Φ) "AU". iMod "AU" as (pl nl) "[[HIsSeg #HIsNextLoc] [_ HClose]]".
  rename nℓ into nℓ'. iDestructHIsSeg.
  iDestruct (segment_next_location_agree with "HIsNextLoc HNextLoc") as %->.
  wp_load.
  iCloseHIsSeg.
  iModIntro.
  by wp_pures.
Qed.

Theorem segment_next_write_spec γ id (ℓ nℓ: loc) (nl: val):
  <<< ∀ pl nl', is_segment γ id ℓ pl nl' ∗ segment_next_location γ id nℓ >>>
    #nℓ <- nl @ ⊤
  <<< is_segment γ id ℓ pl nl, RET #() >>>.
Proof.
  iIntros (Φ) "AU". iMod "AU" as (pl nl') "[[HIsSeg #HIsNextLoc] [_ HClose]]".
  rename nℓ into nℓ'. iDestructHIsSeg.
  iDestruct (segment_next_location_agree with "HIsNextLoc HNextLoc") as %->.
  wp_store.
  iCloseHIsSeg.
  by iModIntro.
Qed.

Theorem segment_canc_spec γ id (ℓ: loc):
  <<< ∀ pl nl, is_segment γ id ℓ pl nl >>>
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
  <<< ∀ pl nl, is_segment γ id ℓ pl nl ∗ segment_canc_location γ id cℓ >>>
    ! #cℓ @ ⊤
  <<< ∃ (cancelled: nat), is_segment γ id ℓ pl nl ∗
      (∃ cells,
          cancelled_cells γ id cells
          ∗ ⌜cancelled = length (List.filter (fun i => i) (vec_to_list cells))⌝),
      RET #cancelled >>>.
Proof.
  iIntros (Φ) "AU". iMod "AU" as (pl nl) "[[HIsSeg #HIsCancLoc] [_ HClose]]".
  rename cℓ into cℓ'. iDestructHIsSeg.
  iDestruct (segment_canc_location_agree with "HIsCancLoc HCancLoc") as %->.
  wp_load.
  iMod ("HClose" $! cancelled with "[HCanc Hℓ Hpℓ Hcℓ Hnℓ]") as "HΦ".
  { iDestruct "HCanc" as (cells) "[-> [#HCancelled HCanc]]".
    iSplitL.
    { rewrite /is_segment /is_segment'; eauto 20 with iFrame. }
    iExists cells. iSplit; done.
  }
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

Check option_included.

Theorem segment_canc_incr_spec γ id cid (ℓ cℓ: loc) segments:
  (cid < Pos.to_nat segment_size)%nat ->
  <<< ∀ pl nl, is_segment γ id ℓ pl nl ∗ segment_canc_location γ id cℓ ∗
                              cell_cancellation_handle' γ id cid ∗
                              own γ (● segments) >>>
    FAA #cℓ #1 @ ⊤
  <<< ∃ (cancelled: nat),
        is_segment γ id ℓ pl nl ∗
    (∃ cells,
          cancelled_cells γ id cells
                          ∗ ⌜cancelled = length (List.filter (fun i => i) (vec_to_list cells))⌝) ∗
    (∃ segments', own γ (● segments')),
    RET #cancelled >>>.
Proof.
  iIntros (HCid Φ) "AU".
  iMod "AU" as (pl nl) "[[HIsSeg [#HIsCancLoc [HCancHandle HAuth]]] [_ HClose]]".
  rename cℓ into cℓ'. iDestructHIsSeg.
  iDestruct (segment_canc_location_agree with "HIsCancLoc HCancLoc") as %->.
  iDestruct "HCanc" as (cells) "[-> [#HCancelled HCanc]]".
  rewrite /cell_cancellation_handle' /ias_cell_info'.
  iCombine "HCanc" "HCancHandle" as "HSeg".
  rewrite -ias_segment_info_op.
  rewrite pair_op.
  iMod (own_update_2 with "HAuth HSeg") as "[HAuth HSeg]".
  { apply auth_update.
    apply (let update_list := list_alter (fun _ => Some (Cinl (to_agree ()))) cid in
           let auth_fn x := ((x.1.1, (fun i => i) <$> x.1.2), update_list x.2) in
           let frag_fn x := ((x.1.1, (fun i => i) <$> x.1.2), update_list x.2)
           in list_alter_local_update id auth_fn frag_fn).
    rewrite ias_segment_info_lookup.
    simpl.
    unfold lookup.
    destruct (list_lookup id segments); simpl.
    2: by apply None_local_update.
    repeat rewrite ucmra_unit_right_id.
    apply option_local_update.
    apply prod_local_update; simpl.
    apply prod_local_update_2; simpl.
    {
      destruct u as [[ULocs [UCanc|]] UCells]; simpl.
      2: by apply None_local_update.
      apply option_local_update.
      admit.
    }
    {
      apply list_alter_local_update.
      repeat rewrite list_lookup_op.
      rewrite lookup_app_r replicate_length. rewrite -minus_diag_reverse; simpl.
      2: lia.
      remember (map _ _) as lst'.
      assert (is_Some (list_lookup cid lst')) as [x Hcell].
      { apply lookup_lt_is_Some. subst.
        rewrite map_length. rewrite vec_to_list_length.
        done.
      }
      unfold lookup.
      rewrite Hcell.
      subst lst'.
      apply list_lookup_fmap_inv in Hcell.
      destruct Hcell as [was_cancelled [-> Hcellid]].
      repeat rewrite -Some_op.
      destruct was_cancelled.
      { rewrite /op /cmra_op /=.
        intros n mz Hxv Heq.
        move: Hxv. rewrite Heq.
        simpl.
        destruct mz; simpl.
        destruct c.
        destruct c.
        all: done.
      }
      simpl.
      rewrite Cinr_op.
      apply local_update_total_valid.
      remember (list_lookup _ _) as He.
      intros HeValid _ HeEq.
      assert (forall (A: ucmraT) (a b: A), a ≡ b ∨ a ≼ b -> a ≼ b) as HSimpl.
      { clear. intros. destruct H; auto. unfold included. exists ε.
        rewrite ucmra_unit_right_id. auto. }
      apply option_included in HeEq.
      destruct HeEq as [?|[a [b [Heq1 [Heq2 HeEq]]]]]; subst; first discriminate.
      rewrite Heq2; simpl.
      apply option_local_update.
      apply transitivity with (y := (None, None)).
      { apply delete_option_local_update.
        apply Cinr_exclusive.
        replace ((1/4) ⋅ (3/4))%Qp with 1%Qp.
        1: by apply frac_full_exclusive.
        symmetry.
        apply Qp_quarter_three_quarter.
      }
      apply alloc_option_local_update.
      done.
    }
  }
  wp_faa.
  iMod ("HClose" $! (length (List.filter (fun i => i) (vec_to_list cells)))%nat with "[Hℓ Hpℓ Hcℓ Hnℓ HAuth]") as "HΦ".
  2: by iModIntro.
Abort.

Theorem segment_data_at_spec γ id (ℓ: loc) (ix: nat):
  ⌜ix < Pos.to_nat segment_size⌝ -∗
  <<< ∀ pl nl, is_segment γ id ℓ pl nl >>>
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
  iMod ("HClose" with "[HCanc Hℓ Hpℓ Hcℓ Hnℓ]") as "HΦ".
  { rewrite /is_segment /is_segment'.
    iAssert (cell_invariant (id * Pos.to_nat segment_size + ix)%nat
                            (dℓ +ₗ ix)) as "#HCellInv".
    { iApply (big_sepL_elem_of with "HCells").
      apply elem_of_list_In. apply in_seq. lia. }
    rewrite /array_mapsto'.
    by eauto 20 with iFrame.
  }
  iModIntro.
  by wp_pures.
Qed.

Theorem new_segment_spec γ (id: nat) pl :
  {{{ is_valid_prev γ id pl }}}
    (new_segment segment_size) #id pl
  {{{ (ℓ dℓ cℓ pℓ nℓ: loc) nl, RET #ℓ;
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
  iSplitL "Hpℓ Hnℓ Hℓ Hcℓ".
  { iSplitR "Hℓ Hcℓ"; iFrame. }
  iSplitL. 2: done.
  rewrite /array.
Abort.

End proof.
