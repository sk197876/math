(** Federer (1969), 2.10.38, printed p. 199: choose an attained diameter in
    the successive projected compact set and lift its endpoints to the
    source. This supporting theorem retains the original source endpoints
    for any Euclidean linear endomorphism. CompactDiameterPair.v records the
    Source context and the general metric maximum background. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerProductUP InnerMetric InnerNorm InnerNormedTopology EuclideanCoordinateTopology
  CompactDiameterPair EuclideanLinearMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_linear_chord_maximum]: supporting
    choice of maximal projected chords and their lifted
    source endpoints in 2.10.38, p. 199.
    Continuity and compactness give attainment without
    assuming convexity or a nonzero diameter. *)
Theorem compact_linear_chord_maximum (R : realType) n
    (S : set (inner_metric_space (@euclidean_inner_productP R n)))
    (P : {linear R_n R n -> R_n R n}) :
  compact S -> S !=set0 -> exists a b,
    S a /\ S b /\ forall x y, S x -> S y ->
    inner_norm (@euclidean_inner_productP R n) (P (x-y))<=
      inner_norm (@euclidean_inner_productP R n) (P (a-b)).
Proof.
move=> hS hne.
pose f : inner_metric_space (@euclidean_inner_productP R n) ->
  inner_metric_space (@euclidean_inner_productP R n) := P.
have hc : compact (f @` S).
  apply: continuous_compact hS.
  apply: continuous_subspaceT.
  exact: (@euclidean_linear_continuous R n P).
have hn : f @` S !=set0 by have [x hx] := hne; exists (f x); exists x.
have [a [b [ha [hb [_ hmax]]]]] := compact_metric_diameter_pair hc hn.
have [a0 ha0 hae] := ha.
have [b0 hb0 hbe] := hb.
exists a0,b0; split=> //; split=> // x y hx hy.
have hh := hmax (f x) (f y) (ex_intro2 _ _ x hx erefl) (ex_intro2 _ _ y hy erefl).
by rewrite -hae -hbe !inner_metric_distanceE -!linearB in hh.
Qed.
