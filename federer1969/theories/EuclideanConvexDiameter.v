(** Metric adapter for the convex-cover alternative in Federer (1969),
    2.10.3, p. 172. Federer 2.10.2(1), p. 171, states that convex hulls
    preserve normed metric diameter. The abstract pair-bound proof is
    already available; apply it to the actual Euclidean metric, keeping its
    carrier distinct from the wrapper for an arbitrary given norm. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerNormInequalities
  InnerMetric RealNormUP ConvexHull NormConvexHullDiameter MetricDiameterUP MetricDiameter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_metric_diameter_convex_hull]:
    supporting Euclidean instance of the diameter identity
    in Federer 2.10.2(1), p. 171, for the size
    restriction on convex covers in 2.10.3, p. 172.
    Empty sets, infinite diameter and dimension zero
    are included. *)
Theorem euclidean_metric_diameter_convex_hull (R : realType) (n : nat) (A : set (R_n R n)) :
  @extended_metric_diameter R (inner_metric_space (@euclidean_inner_productP R n))
    (@convex_hull R (R_n R n) A)=
  @extended_metric_diameter R (inner_metric_space (@euclidean_inner_productP R n)) A.
Proof.
pose N := inner_norm (@euclidean_inner_productP R n).
have hN : is_real_norm N.
  split.
  - split; [exact: inner_norm_nonnegative|exact: inner_normZ|exact: inner_norm_triangle].
  - move=> x hx; rewrite /N in hx; apply/eqP.
    by rewrite -(inner_norm_eq0 (@euclidean_inner_productP R n)) hx eqxx.
apply/eqP; rewrite eq_le; apply/andP; split; last first.
  exact (@extended_metric_diameter_mono R (inner_metric_space (@euclidean_inner_productP R n))
    A (@convex_hull R (R_n R n) A) (@convex_hull_includes R (R_n R n) A)).
have hA := @extended_metric_diameter_specification R (inner_metric_space (@euclidean_inner_productP R n)) A.
apply: (metric_diameter_least (@extended_metric_diameter_specification R
  (inner_metric_space (@euclidean_inner_productP R n)) (@convex_hull R (R_n R n) A))
  (metric_diameter_nonnegative hA))=> x y hx hy.
case he: (@extended_metric_diameter R (inner_metric_space (@euclidean_inner_productP R n)) A)
    hA=> [r| |] hA.
- rewrite lee_fin inner_metric_distanceE.
  apply: (@convex_hull_preserves_pair_bound R (R_n R n) N hN A r _ x y hx hy).
  move=> a b ha hb; have hh := metric_diameter_upper hA ha hb.
  by move: hh; rewrite lee_fin inner_metric_distanceE.
- exact: leey.
- by have := metric_diameter_nonnegative hA.
Qed.
