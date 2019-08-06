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

From iris.algebra Require Import cmra auth list agree csum.

Section proof.

Notation cancellable_cell_algebra := (prodUR (optionUR (agreeR locO))
                                             (optionUR (csumR (agreeR unitO)
                                                              positiveR
                                     ))).

Notation cell_algebra := (prodUR cancellable_cell_algebra
                                 (optionUR (agreeR gnameO))).

Notation segment_algebra := (prodUR cancellable_cell_algebra
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

Definition ias_segment_info (id: nat) (s: segment_algebra):
  listUR segment_algebra :=
  replicate (id * Pos.to_nat segment_size) (None, None, nil) ++ [s].

Definition ias_cell_info (id: nat) (c: cell_algebra): listUR segment_algebra :=
  let ns := (id `div` Pos.to_nat segment_size)%nat in
  let nc := (id `mod` Pos.to_nat segment_size)%nat in
  ias_segment_info ns (None, None, replicate nc (None, None, None) ++ [c]).

Theorem list_core_id' {A: ucmraT} (l: listUR A) :
  (forall x, x ∈ l -> CoreId x) -> CoreId l.
Proof.
  intros Hyp. constructor. apply list_equiv_lookup=> i.
  rewrite list_lookup_core.
  destruct (l !! i) eqn:E; rewrite E.
  2: done.
  apply Hyp.
  eapply elem_of_list_lookup; by eauto.
Qed.

Theorem ias_segment_info_core_id (id: nat) (s: segment_algebra):
  CoreId s -> CoreId (ias_segment_info id s).
Proof.
  intro SegHyp.
  rewrite /ias_segment_info.
  apply list_core_id'.
  intros ? HElemOf.
  induction (id * Pos.to_nat segment_size)%nat; simpl in *.
  - inversion HElemOf; first done.
    exfalso. by eapply not_elem_of_nil.
  - inversion HElemOf; first by apply _.
    by apply IHn.
Qed.

Theorem ias_cell_info_core_id (id: nat) (c: cell_algebra):
  CoreId c -> CoreId (ias_cell_info id c).
Proof.
  intro CellHyp.
  rewrite /ias_cell_info.
  apply ias_segment_info_core_id.
  apply pair_core_id; first by apply _.
  apply list_core_id'.
  induction (id `mod` Pos.to_nat segment_size)%nat; intros ? HElemOf; simpl in *.
  - inversion HElemOf; first by apply _.
    exfalso. by eapply not_elem_of_nil.
  - inversion HElemOf; first by apply _.
    by apply IHn.
Qed.

Definition array_mapsto γ (n: nat) (ℓ: loc): iProp :=
  own γ (◯ (ias_cell_info n (Some (to_agree ℓ), None, None))).

Theorem array_mapsto_persistent γ n ℓ: Persistent (array_mapsto γ n ℓ).
Proof.
  apply own_core_persistent.
  apply auth_frag_core_id.
  apply ias_cell_info_core_id.
  apply pair_core_id; apply _.
Qed.

Definition segment_is_cancelled γ (n: nat): iProp :=
  own γ (◯ (ias_segment_info n (None, Some (Cinl (to_agree tt)), nil))).

Theorem segment_is_cancelled_persistent γ n:
  Persistent (segment_is_cancelled γ n).
Proof.
  apply own_core_persistent.
  apply auth_frag_core_id.
  apply ias_segment_info_core_id.
  apply pair_core_id; apply _.
Qed.

Definition cell_is_cancelled γ (n: nat): iProp :=
  own γ (◯ (ias_cell_info n (None, Some (Cinl (to_agree tt)), None))).

Theorem cell_is_cancelled_persistent γ n:
  Persistent (cell_is_cancelled γ n).
Proof.
  apply own_core_persistent.
  apply auth_frag_core_id.
  apply ias_cell_info_core_id.
  apply pair_core_id; apply _.
Qed.

Definition segments_mapto (locs: list loc): listUR segment_algebra :=
  (fun ℓ => (Some (to_agree ℓ), None, nil)) <$> locs.

Definition ias_segment_contains_cells (id: nat)
           (locs: vec loc (Pos.to_nat segment_size)): listUR segment_algebra :=
  ias_segment_info id (None, None,
                   (fun ℓ => (Some (to_agree ℓ), None, None)) <$> vec_to_list locs).

Definition is_valid_prev γ (id: nat) (pl: val): iProp :=
  (⌜pl = NONEV⌝ ∧
   ([∗ list] j ∈ seq 0 (id * Pos.to_nat segment_size),
    cell_is_cancelled γ j ∨ cell_is_done j) ∨
   ∃ (segment_locs: list loc),
     own γ (◯ (segments_mapto segment_locs)) ∗
   ∃ (pid: nat),
     ⌜Some pl = option_map (LitV ∘ LitLoc) (segment_locs !! pid)⌝ ∧
     ⌜pid < id⌝ ∧
     [∗ list] j ∈ seq (S pid) id, segment_is_cancelled γ j)%I.

Definition is_valid_next γ (id: nat) (nl: val): iProp :=
  (∃ (segment_locs: list loc),
     own γ (◯ (segments_mapto segment_locs)) ∗
   ∃ (nid: nat),
      ⌜Some nl = option_map (fun x => LitV (LitLoc x)) (segment_locs !! nid)⌝ ∧
      ⌜id < nid⌝ ∧
      [∗ list] j ∈ seq (S id) nid, segment_is_cancelled γ j)%I.

Definition ias_cell_is_cancelled (cell: cell_algebra) :=
    exists t, cell.1.2 = Some (Cinl t).

Instance cell_is_cancelled_dec : forall (cell: cell_algebra),
    Decision (ias_cell_is_cancelled cell).
Proof.
  intros.
  rewrite /ias_cell_is_cancelled.
  destruct cell as [[tmp1 cancelled_info] tmp2].
  simpl.
  destruct cancelled_info as [cancelled_info|].
  1: destruct cancelled_info; simpl.
  1: left; by eauto.
  all: right; intro Contra; destruct Contra as [t HContra]; discriminate.
Qed.

Definition is_segment γ (id: nat)
           (cancelled: nat) (ℓ: loc) (pl nl: val) : iProp :=
  ((⌜cancelled = Pos.to_nat segment_size⌝ ∧
    segment_is_cancelled γ id ∨
    ⌜cancelled < Pos.to_nat segment_size⌝ ∧
    ∃ (cells: listUR cell_algebra),
      own γ (◯ (ias_segment_info id (None, None, cells)))
          ∗ ⌜length (filter ias_cell_is_cancelled cells) = cancelled⌝)
     ∗ (∃ (dℓ: loc) (locs: vec loc (Pos.to_nat segment_size)),
           own γ (◯ (ias_segment_contains_cells id locs)) ∗
           ℓ ↦ (((#id, #cancelled), #dℓ), (pl, nl)) ∗
             dℓ ↦∗ map (LitV ∘ LitLoc) (vec_to_list locs))
     ∗ is_valid_prev γ id pl)%I.

Definition is_normal_segment γ (ℓ: loc) (id: nat)
           (cancelled: nat)
           (pl nl: val): iProp :=
  (is_segment γ id cancelled ℓ pl nl ∗ is_valid_next γ id nl)%I.

Definition is_tail_segment γ (ℓ: loc) (id: nat)
           (cancelled: nat) (pl: val): iProp :=
  is_segment γ id cancelled ℓ pl NONEV.

(*)
Definition is_infinite_array γ
      (∃ (relevant_locs : list loc) (pl nl : val),
      own γ (map_to relevant_locs nil) ∗
      ∧
      is_segment id locs ℓ pl nl)
*)

End proof.
