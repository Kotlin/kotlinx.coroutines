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

Notation segment_algebra := (prodUR (prodUR (optionUR (agreeR locO))
                                            (optionUR (csumR (agreeR unitO)
                                                             positiveR
                                            ))
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

Definition ias_segment_info (id: nat) (s: segment_algebra):
  listUR segment_algebra :=
  replicate (id * Pos.to_nat segment_size) (None, None, nil) ++ [s].

Definition ias_cell_info' (id_seg id_cell: nat) (c: cell_algebra):
  listUR segment_algebra :=
  ias_segment_info id_seg (None, None, replicate id_cell None ++ [c]).

Definition ias_cell_info (id: nat) (c: cell_algebra): listUR segment_algebra :=
  let ns := (id `div` Pos.to_nat segment_size)%nat in
  let nc := (id `mod` Pos.to_nat segment_size)%nat in
  ias_cell_info' ns nc c.

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

Global Instance ias_segment_info_core_id (id: nat) (s: segment_algebra):
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

Global Instance ias_cell_info_core_id (ids idc: nat) (c: cell_algebra):
  CoreId c -> CoreId (ias_cell_info' ids idc c).
Proof.
  intro CellHyp.
  rewrite /ias_cell_info.
  apply ias_segment_info_core_id.
  apply pair_core_id; first by apply _.
  apply list_core_id'.
  induction idc; intros ? HElemOf; simpl in *.
  - inversion HElemOf; first by apply _.
    exfalso. by eapply not_elem_of_nil.
  - inversion HElemOf; first by apply _.
    by apply IHidc.
Qed.

Theorem ias_cell_info__ias_cell_info' ns nc n s:
  (nc < Pos.to_nat segment_size)%nat ->
  n = (nc + ns * Pos.to_nat segment_size)%nat ->
  ias_cell_info' ns nc s = ias_cell_info n s.
Proof.
  rewrite /ias_cell_info /ias_cell_info'.
  intros Hlt Heq.
  subst.
  replace ((nc + ns * Pos.to_nat segment_size) `div` Pos.to_nat segment_size)%nat
    with ns.
  replace ((nc + ns * Pos.to_nat segment_size) `mod` Pos.to_nat segment_size)%nat
    with nc.
  done.
  {
    rewrite Nat.mod_add.
    by rewrite Nat.mod_small.
    assert (O < Pos.to_nat segment_size)%nat by apply Pos2Nat.is_pos; lia.
  }
  {
    rewrite Nat.div_add.
    by rewrite Nat.div_small.
    assert (O < Pos.to_nat segment_size)%nat by apply Pos2Nat.is_pos; lia.
  }
Qed.

Definition array_mapsto' γ ns nc ℓ: iProp :=
  ((∃ (dℓ: loc), ⌜ℓ = dℓ +ₗ Z.of_nat nc⌝ ∧
                 own γ (◯ (ias_segment_info
                             ns ((Some (to_agree dℓ)), None, nil)))))%I.

Global Instance array_mapsto'_persistent γ ns nc ℓ:
  Persistent (array_mapsto' γ ns nc ℓ).
Proof.
  apply bi.exist_persistent; intros;
    apply bi.and_persistent; first by apply _.
  apply own_core_persistent; apply auth_frag_core_id;
    apply ias_segment_info_core_id; apply pair_core_id; apply _.
Qed.

Definition array_mapsto γ (id: nat) (ℓ: loc): iProp :=
  let ns := (id `div` Pos.to_nat segment_size)%nat in
  let nc := (id `mod` Pos.to_nat segment_size)%nat in
  array_mapsto' γ ns nc ℓ.

Theorem array_mapsto'_agree γ (ns nc: nat) (ℓ ℓ': loc):
  array_mapsto' γ ns nc ℓ -∗ array_mapsto' γ ns nc ℓ' -∗ ⌜ℓ = ℓ'⌝.
Proof.
  rewrite /array_mapsto'.
  iIntros "Ham Ham'".
  iDestruct "Ham" as (dℓ) "[% Ham]".
  iDestruct "Ham'" as (dℓ') "[% Ham']".
  subst.
  iDestruct (own_valid_2 with "Ham Ham'") as %Hv.
  rewrite /ias_segment_info -auth_frag_op in Hv.
  assert (forall (A: ucmraT) (a: A), ✓ (◯ a) -> ✓a) as Hauth_frag_valid.
  { by intros; apply auth_frag_valid. }
  apply Hauth_frag_valid in Hv. clear Hauth_frag_valid.
  assert (forall (i: nat) (A: ucmraT) (l: list A), ✓ l -> ✓ (l !! i)) as Hlist_valid.
  { by intros; apply list_lookup_valid. }
  remember (ns * Pos.to_nat segment_size)%nat as k.
  apply (Hlist_valid k) in Hv. clear Hlist_valid.
  assert (forall A k (a: A) c, (replicate k c ++ [a]) !! k = Some a) as Hrep.
  { clear. intros. induction k; auto. }
  rewrite list_lookup_op in Hv.
  rewrite Hrep in Hv.
  rewrite Hrep in Hv.
  destruct Hv as [[Hp _] _]; simpl in *.
  compute in Hp.
  specialize (Hp O dℓ dℓ').
  rewrite Hp; eauto; repeat constructor.
Qed.

Theorem array_mapsto_agree γ n (ℓ ℓ': loc):
  array_mapsto γ n ℓ -∗ array_mapsto γ n ℓ' -∗ ⌜ℓ = ℓ'⌝.
Proof. apply array_mapsto'_agree. Qed.

Global Instance array_mapsto_persistent γ n ℓ: Persistent (array_mapsto γ n ℓ).
Proof. apply _. Qed.

Definition segment_is_cancelled γ (n: nat): iProp :=
  own γ (◯ (ias_segment_info n (None, Some (Cinl (to_agree tt)), nil))).

Global Instance segment_is_cancelled_persistent γ n:
  Persistent (segment_is_cancelled γ n).
Proof.
  apply own_core_persistent.
  apply auth_frag_core_id.
  apply ias_segment_info_core_id.
  apply pair_core_id; apply _.
Qed.

Definition cell_is_cancelled γ (n: nat): iProp :=
  own γ (◯ (ias_cell_info n (Some (Cinl (to_agree tt))))).

Global Instance cell_is_cancelled_persistent γ n:
  Persistent (cell_is_cancelled γ n).
Proof. apply _. Qed.

Definition segments_mapto γ (locs: list loc): iProp :=
  own γ (◯ ((fun ℓ => (Some (to_agree ℓ), None, nil)) <$> locs)).

Global Instance segments_mapto_persistent γ locs:
  Persistent (segments_mapto γ locs).
Proof.
  apply own_core_persistent.
  apply auth_frag_core_id.
  apply list_core_id'.
  intros ? Hel.
  destruct x as [[RLoc RCanc] RNil].
  assert (RNil = [] /\ RCanc = None) as [HRNil HRCanc].
  { induction locs; inversion Hel; auto. }
  subst.
  apply _.
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

Definition is_segment γ (id: nat) (ℓ: loc) (pl nl: val) : iProp :=
  (∃ cancelled,
      (∃ (cells: vec bool (Pos.to_nat segment_size)),
          ⌜cancelled = length (List.filter (fun i => i) (vec_to_list cells))⌝ ∗
          let uncancelled := (Pos.to_nat segment_size - cancelled)%nat in
          own γ (◯ (ias_segment_info
                      id
                      (None,
                        Some (if Nat.eqb uncancelled O
                              then Cinl (to_agree tt)
                              else Cinr (Pos.of_nat uncancelled)),
                        map (fun (c: bool) =>
                              (Some (if c
                                      then Cinl (to_agree tt)
                                      else Cinr (1/4)%Qp)))
                            (vec_to_list cells)))))
        ∗ (∃ (dℓ: loc), ℓ ↦ (((#id, #cancelled), #dℓ), (pl, nl)) ∗
                          ([∗ list] i ∈ seq 0 (Pos.to_nat segment_size),
                           cell_invariant (id*Pos.to_nat segment_size+i)%nat
                                          (dℓ +ₗ Z.of_nat i)))
        ∗ is_valid_prev γ id pl)%I.

Definition is_normal_segment γ (ℓ: loc) (id: nat): iProp :=
  (∃ pl nl, is_segment γ id ℓ pl nl ∗ is_valid_next γ id nl)%I.

Definition is_tail_segment γ (ℓ: loc) (id: nat): iProp :=
  (∃ pl, is_segment γ id ℓ pl NONEV)%I.

Definition is_infinite_array γ : iProp :=
  (∃ segments, ([∗ list] i ↦ ℓ ∈ segments, is_normal_segment γ ℓ i)
                 ∗ (∃ ℓ, is_tail_segment γ ℓ (length segments))
                 ∗ (∃ segments', ⌜S (length segments) = length segments'⌝ ∧
                                 own γ (● segments')))%I.

Definition does_point_to_segment γ ℓ id: iProp :=
  own γ (◯ (ias_segment_info id (Some (to_agree ℓ), None, nil))).

Global Instance does_point_to_segment_persistent γ ℓ id:
  Persistent (does_point_to_segment γ ℓ id).
Proof.
  apply own_core_persistent.
  apply auth_frag_core_id.
  apply ias_segment_info_core_id.
  apply pair_core_id; apply _.
Qed.

Theorem segment_id_spec γ id (ℓ: loc):
  <<< ∀ pl nl, is_segment γ id ℓ pl nl >>>
    segment_id #ℓ @ ⊤
  <<< is_segment γ id ℓ pl nl, RET #id >>>.
Proof.
  iIntros (Φ) "AU". wp_lam.
  wp_bind (!_)%E. iMod "AU" as (pl nl) "[HIsSeg [_ HClose]]".
  iDestruct "HIsSeg" as (cancelled) "[HCanc [HMem #HValidPrev]]".
  iDestruct "HMem" as (dℓ) "[Hℓ #HCells]".
  wp_load.
  iMod ("HClose" with "[HCanc Hℓ]") as "HΦ".
  { rewrite /is_segment; by eauto 10 with iFrame. }
  iModIntro.
  by wp_pures.
Qed.

Theorem segment_prev_spec γ id (ℓ: loc):
  <<< ∀ pl nl, is_segment γ id ℓ pl nl >>>
    segment_prev #ℓ @ ⊤
  <<< is_segment γ id ℓ pl nl ∗ is_valid_prev γ id pl, RET pl >>>.
Proof.
  iIntros (Φ) "AU". wp_lam.
  wp_bind (!_)%E. iMod "AU" as (pl nl) "[HIsSeg [_ HClose]]".
  iDestruct "HIsSeg" as (cancelled) "[HCanc [HMem #HValidPrev]]".
  iDestruct "HMem" as (dℓ) "[Hℓ #HCells]".
  wp_load.
  iMod ("HClose" with "[HCanc Hℓ]") as "HΦ".
  { rewrite /is_segment; by eauto 10 with iFrame. }
  iModIntro.
  by wp_pures.
Qed.

Theorem segment_next_spec γ id (ℓ: loc):
  <<< ∀ pl nl, is_segment γ id ℓ pl nl >>>
    segment_next #ℓ @ ⊤
  <<< is_segment γ id ℓ pl nl, RET nl >>>.
Proof.
  iIntros (Φ) "AU". wp_lam.
  wp_bind (!_)%E. iMod "AU" as (pl nl) "[HIsSeg [_ HClose]]".
  iDestruct "HIsSeg" as (cancelled) "[HCanc [HMem #HValidPrev]]".
  iDestruct "HMem" as (dℓ) "[Hℓ #HCells]".
  wp_load.
  iMod ("HClose" with "[HCanc Hℓ]") as "HΦ".
  { rewrite /is_segment; by eauto 10 with iFrame. }
  iModIntro.
  by wp_pures.
Qed.

Theorem segment_data_at_spec γ id (ℓ: loc) (ix: nat):
  ⌜ix < Pos.to_nat segment_size⌝ -∗
  <<< ∀ pl nl, is_segment γ id ℓ pl nl >>>
    segment_data_at #ℓ #ix @ ⊤
  <<< ∃ (v: loc), is_segment γ id ℓ pl nl
                             ∗ array_mapsto' γ id ix v
                             ∗ cell_invariant (id * Pos.to_nat segment_size + ix)%nat v, RET #v >>>.
Proof.
  iIntros "%". iIntros (Φ) "AU". wp_lam. wp_pures.
  wp_bind (!_)%E. iMod "AU" as (pl nl) "[HIsSeg [_ HClose]]".
  iDestruct "HIsSeg" as (cancelled) "[HCanc [HMem #HValidPrev]]".
  iDestruct "HMem" as (dℓ) "[Hℓ #HCells]".
  wp_load.
  iSpecialize ("HClose" $! (dℓ +ₗ ix)).
  iMod ("HClose" with "[HCanc Hℓ]") as "HΦ".
  { rewrite /is_segment.
    iAssert (cell_invariant (id * Pos.to_nat segment_size + ix)%nat
                            (dℓ +ₗ ix)) as "#HCellInv".
    {
      iApply (big_sepL_elem_of with "HCells").
      apply elem_of_list_In.
      apply in_seq.
      lia.
    }
    iSplitL.
    2: {
      iSplitL.
      2: by iApply "HCellInv".
      rewrite /array_mapsto'.
      iExists _.
      iSplitL; eauto.
      admit.
    }
    admit.
  }
  iModIntro.
  by wp_pures.
Abort.

(*
Definition segment_cancelled : val :=
  λ: "seg", Snd (Fst (Fst !"seg")).
*)

End proof.
