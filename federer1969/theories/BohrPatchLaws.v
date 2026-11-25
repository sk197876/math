(** Consequences of the local patch laws supporting Federer
    (1969), 2.8.20, p. 152. These arguments use
    only the abstract predicate, not the coordinate witness.
    The finite remaining regions are those in Saks1934 Lemma B,
    p. 258, and Cesari1939 Lemma III, p. 306.
    Source titles and comparisons: VitaliMassObstruction.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal.
From Federer Require Import ScalarPlaneRectangles ScalarHalfOpenRectangles
  BohrPatchUP FiniteHalfOpenPartitionUP FiniteHalfOpenPartitions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [rectangle_companions_half_open]: the auxiliary
    cell in the construction for Federer 2.8.20, p. 152,
    has positive sides, as specified by its companion laws. *)
Lemma rectangle_companions_half_open (R : realType) (H K : set (R*R)) :
  are_rectangle_companions H K -> is_nondegenerate_half_open_rectangle H.
Proof.
move=> [a [b [c [d [hab [hcd [-> _]]]]]]]; by exists a,b,c,d; split=> //; split.
Qed.

(** Source for [rectangle_companions_closed]: eligible closed
    cells in Federer 2.8.20, p. 152, have positive
    sides. This is a consequence of the companion predicate. *)
Lemma rectangle_companions_closed (R : realType) (H K : set (R*R)) :
  are_rectangle_companions H K -> is_nondegenerate_scalar_rectangle K.
Proof.
move=> [a [b [c [d [hab [hcd [_ ->]]]]]]]; by exists a,b,c,d; split=> //; split.
Qed.

(** Source for [rectangle_companions_inclusion]: auxiliary
    half-open cells lie in their closed eligible companions
    for Federer 2.8.20, p. 152. *)
Lemma rectangle_companions_inclusion (R : realType) (H K : set (R*R)) :
  are_rectangle_companions H K -> H `<=` K.
Proof.
move=> [a [b [c [d [_ [_ [-> ->]]]]]]]; exact: half_open_rectangle_within_closed.
Qed.

(** Source for [rectangle_companions_area]: closed eligible
    and half-open auxiliary cells have the same finite area
    in the construction for Federer 2.8.20, p. 152. *)
Lemma rectangle_companions_area (R : realType) (H K : set (R*R)) :
  are_rectangle_companions H K -> scalar_plane_lebesgue H = scalar_plane_lebesgue K.
Proof.
move=> [a [b [c [d [hab [hcd [-> ->]]]]]]].
by rewrite scalar_half_open_rectangle_value ?ltW // scalar_closed_rectangle_value ?ltW.
Qed.

(** Source for [bohr_patch_remainder_partition]: finite
    remaining rectangular regions after inserting one group
    for Federer 2.8.20, p. 152; Saks1934 Lemma B,
    p. 258. Finite-group removal follows from the
    sealed one-rectangle difference laws. *)
Lemma bohr_patch_remainder_partition (R : realType) (Q : set (R*R)) r
    (H K : 'I_r -> set (R*R)) (E : set (R*R)) :
  is_bohr_patch Q H K E ->
  exists G, is_finite_half_open_partition (Q `\` (\bigcup_(i in @setT 'I_r) H i)) G.
Proof.
move=> hp.
have hfin : finite_set (H @` setT) := @finite_image _ _ setT H (@finite_finset _ setT).
have hrect S : (H @` setT) S -> is_nondegenerate_half_open_rectangle S.
  move=> [i _ <-]; apply: rectangle_companions_half_open.
  exact: bohr_patch_companions hp i.
have [G hG] := @finite_half_open_partition_remove_family R Q [set Q] (H @` setT)
  (singleton_half_open_partition (bohr_patch_parent hp)) hfin hrect.
have he : (\bigcup_(S in H @` setT) S) = (\bigcup_(i in @setT 'I_r) H i).
  apply/seteqP; split=> [x [S [i _ <-] hx]|x [i _ hx]]; [by exists i|exists (H i)=> //; by exists i].
by rewrite he in hG; exists G.
Qed.
