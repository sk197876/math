(** Federer (1969), 3.3.20, pp. 306–308:
    the original square lies in every original Cartesian level. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CompactIntervalGauge SpecialIntervalFamilyUP
  BinaryCantorSquareLevelsUP EuclideanInnerProduct InnerMetric EuclideanRealPlane
  EuclideanCantorProduct EuclideanIntervalRectangles.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [binary_cantor_original_square_level_cover]:
    E is contained in the union of the
    ACTUAL G_j squares, 3.3.20, pp. 306–308.
    The original intersection-limit laws supply both
    coordinates at every level. *)
Lemma binary_cantor_original_square_level_cover (R:realType)
    (H:nat->{fset compact_real_intervals R}) G (A:set (real_line_metric R)):
  is_special_interval_tree_limit H A ->is_binary_cantor_square_levels H G ->
  forall j x,euclidean_cantor_product A A x ->
    exists P,P \in G j /\euclidean_interval_rectangle P.1 P.2 x.
Proof.
move=>hA hG j x [hx hy].
have [S [hS hxS]]:=(hA _).1 hx j.
have [T [hT hyT]]:=(hA _).1 hy j.
exists (S,T);split;first by rewrite hG in_fsetM hS hT.
by split.
Qed.
