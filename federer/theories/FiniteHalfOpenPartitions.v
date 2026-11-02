(** Public finite partition operations supporting Federer
    (1969), 2.8.20, p. 152. The finite remaining
    regions of Saks1934 Lemma B, p. 258, and
    Cesari1939 Lemma III, p. 306, are assembled from
    sealed rectangle-difference partitions. No computation
    through the private grid is used here. Source titles:
    VitaliMassObstruction.v. *)
From mathcomp Require Import all_boot boolp classical_sets cardinality reals.
From Federer Require Import ScalarHalfOpenRectangles CountablyClosedFamilyUP
  FiniteHalfOpenPartitionUP HalfOpenRectangleDifferenceSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [empty_half_open_partition]: empty remainder
    boundary for the finite packing supporting Federer
    2.8.20, p. 152. No ambient point is selected. *)
Lemma empty_half_open_partition (R : realType) :
  is_finite_half_open_partition (@set0 (R*R)) set0.
Proof.
constructor.
- exact: finite_set0.
- by move=> S [].
- by move=> S T [].
- exact: bigcup_set0.
Qed.

(** Source for [singleton_half_open_partition]: one-region
    initial partition for the finite packing supporting
    Federer 2.8.20, p. 152. The region is a
    positive half-open coordinate rectangle. *)
Lemma singleton_half_open_partition (R : realType) (A : set (R*R)) :
  is_nondegenerate_half_open_rectangle A -> is_finite_half_open_partition A [set A].
Proof.
move=> hA; constructor.
- exact: finite_set1.
- by move=> S ->.
- move=> S T -> -> hne; exfalso; exact: hne (erefl _).
- exact: bigcup_set1.
Qed.

(** Source for [finite_half_open_partition_glue_difference]:
    supporting assembly of remaining regions in the finite
    Bohr packing for Federer 2.8.20, p. 152.
    Replace each disjoint parent cell by a finite partition
    of its difference from B. The assembled partition is
    finite, disjoint and covers exactly A minus B. *)
Theorem finite_half_open_partition_glue_difference (R : realType)
    (A B : set (R*R)) (G : set (set (R*R)))
    (H : set (R*R) -> set (set (R*R))) :
  is_finite_half_open_partition A G ->
  (forall S, G S -> is_finite_half_open_partition (S `\` B) (H S)) ->
  is_finite_half_open_partition (A `\` B) (\bigcup_(S in G) H S).
Proof.
move=> hp hH; constructor.
- apply: bigcup_finite; first exact: half_open_partition_finite hp.
  move=> S hS; exact: half_open_partition_finite (hH S hS).
- move=> U [S hS hU]; exact (@half_open_partition_rectangles R (S `\` B) (H S) (hH S hS) U hU).
- move=> U V [S hS hU] [T hT hV] hne.
  case: (pselect (S=T))=> [he|hST].
  + subst T; exact (@half_open_partition_disjoint R (S `\` B) (H S) (hH S hS) U V hU hV hne).
  + apply/seteqP; split=> [x [hxU hxV]|x []].
    have hxS := (@half_open_partition_member_subset R (S `\` B) (H S) (hH S hS) U hU x hxU).1.
    have hxT := (@half_open_partition_member_subset R (T `\` B) (H T) (hH T hT) V hV x hxV).1.
    have hd := @half_open_partition_disjoint R A G hp S T hS hT hST.
    have hx : (S `&` T) x by split.
    by rewrite hd in hx.
- apply/seteqP; split.
  + move=> x [U [S hS hU] hxU].
    have [hxS hnB] := @half_open_partition_member_subset R (S `\` B) (H S) (hH S hS) U hU x hxU.
    split=> //; rewrite -(half_open_partition_union hp); by exists S.
  + move=> x [hxA hnB].
    have hxG : (\bigcup_(S in G) S) x by rewrite (half_open_partition_union hp).
    have [S hS hxS] := hxG.
    have hxH : (\bigcup_(U in H S) U) x by rewrite (half_open_partition_union (hH S hS)); split.
    have [U hU hxU] := hxH; exists U=> //; by exists S.
Qed.

(** Source for [finite_half_open_partition_difference]:
    supporting finite stability under removing a positive
    half-open rectangle in the construction for Federer
    2.8.20, p. 152. Select the proved difference
    partition for each parent and use its abstract laws only. *)
Theorem finite_half_open_partition_difference (R : realType)
    (A B : set (R*R)) (G : set (set (R*R))) :
  is_finite_half_open_partition A G -> is_nondegenerate_half_open_rectangle B ->
  exists K, is_finite_half_open_partition (A `\` B) K.
Proof.
move=> hp hB.
have hex S : exists K, G S -> is_finite_half_open_partition (S `\` B) K.
  case: (pselect (G S))=> hS.
  - have hr := @half_open_partition_rectangles R A G hp S hS.
    exists (@HalfOpenRectangleDifference.value R S B hr hB)=> _.
    exact: HalfOpenRectangleDifference.laws.
  - exists set0=> h; exfalso; exact: hS h.
pose H S := projT1 (cid (hex S)).
have hH S := projT2 (cid (hex S)).
exists (\bigcup_(S in G) H S).
exact (@finite_half_open_partition_glue_difference R A B G H hp hH).
Qed.

(** Source for [finite_half_open_partition_remove_list]:
    supporting stability of the remaining regions when removing
    a whole finite rectangular group in Federer 2.8.20,
    p. 152; Saks1934 Lemma B, p. 258.
    Successive removal uses only the sealed difference laws. *)
Theorem finite_half_open_partition_remove_list (R : realType)
    (A : set (R*R)) (G : set (set (R*R))) (s : seq (set (R*R))) :
  is_finite_half_open_partition A G ->
  (forall B, B \in s -> is_nondegenerate_half_open_rectangle B) ->
  exists K, is_finite_half_open_partition (A `\` (\bigcup_(B in [set` s]) B)) K.
Proof.
elim: s A G=> [|B s ih] A G hp hs.
- have he : (\bigcup_(B in [set` ([::] : seq (set (R*R)))]) B) = set0.
    apply/seteqP; split=> [x [B hB _]|x []]; by move: hB; rewrite /= inE.
  by rewrite he setD0; exists G.
- have hB : is_nondegenerate_half_open_rectangle B by apply: hs; rewrite inE eqxx.
  have [G' hp'] := @finite_half_open_partition_difference R A B G hp hB.
  have hs' C : C \in s -> is_nondegenerate_half_open_rectangle C.
    move=> hC; apply: hs; by rewrite inE hC orbT.
  have [K hK] := ih (A `\` B) G' hp' hs'.
  have he : A `\` (\bigcup_(C in [set` B::s]) C) =
      (A `\` B) `\` (\bigcup_(C in [set` s]) C).
    apply/seteqP; split.
    + move=> x [hx hn]; split.
      * split=> // hB'; apply: hn; exists B=> //; by rewrite /= inE eqxx.
      * move=> [C hC hxC]; apply: hn; exists C=> //; by rewrite /= inE hC orbT.
    + move=> x [[hx hnB] hnS]; split; first exact hx.
      move=> [C hC hxC].
      move: hC; rewrite /= inE=> /orP [/eqP heC|hC].
      * subst C; exact: hnB hxC.
      *
      apply: hnS; by exists C.
  by rewrite he; exists K.
Qed.

(** Source for [finite_half_open_partition_remove_family]:
    supporting finite-group removal for Federer 2.8.20,
    p. 152. Finiteness supplies a list only inside
    this proof; no enumeration is part of the specification. *)
Theorem finite_half_open_partition_remove_family (R : realType)
    (A : set (R*R)) (G F : set (set (R*R))) :
  is_finite_half_open_partition A G -> finite_set F ->
  (forall B, F B -> is_nondegenerate_half_open_rectangle B) ->
  exists K, is_finite_half_open_partition (A `\` (\bigcup_(B in F) B)) K.
Proof.
move=> hp /finite_seqP [s ->] hs.
apply: finite_half_open_partition_remove_list hp _.
by move=> B hB; apply: hs; exact: hB.
Qed.
