(** Completion of the minimal-radius argument in Federer (1969), 2.10.31,
    pp. 195–196. A positive-radius minimiser is the whole closed ball. Use
    radial segments through zero, a permissible explicit choice of the
    printed line L. The proof also covers the origin point by normalising a
    point attaining the positive radius, so no positive-dimensional
    assumption is added. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import InnerProductUP InnerNorm InnerMetric InnerNormalization
  CompactSetDistanceProfile CompactHausdorffMetric CompactEnclosingRadius MetricClosedBalls
  LipschitzFunctionCompact SteinerStableFamilyUP SteinerMinimalRadialSegments.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [steiner_positive_minimiser_is_ball]: direct
    final equality S=B(0,r) in 2.10.31,
    p. 196, when the attained minimum is
    positive. The radius-zero alternative is separate. *)
Theorem steiner_positive_minimiser_is_ball (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B)
    (C : set (compact_hausdorff_space (inner_metric_space hB)))
    (S : compact_hausdorff_space (inner_metric_space hB)) :
  metric_boundedly_compact (inner_metric_space hB) ->
  is_steiner_stable_family hB C -> C S ->
  (forall T, C T -> compact_enclosing_radius (0 : inner_metric_space hB) S<=
    compact_enclosing_radius (0 : inner_metric_space hB) T) ->
  0<compact_enclosing_radius (0 : inner_metric_space hB) S ->
  val S=metric_closed_ball (0 : inner_metric_space hB) (compact_enclosing_radius (0 : inner_metric_space hB) S).
Proof.
move=> hX hC hS hmin hr.
pose r := compact_enclosing_radius (0 : inner_metric_space hB) S.
have hb x : val S x -> inner_norm hB x<=r.
  move=> hx; have hh := compact_enclosing_radius_contains (0 : inner_metric_space hB) S x hx.
  by rewrite /metric_closed_ball /= inner_metric_distanceE sub0r inner_normN in hh.
have [a [ha har]] := compact_enclosing_radius_attains (0 : inner_metric_space hB) S.
rewrite inner_metric_distanceE sub0r inner_normN in har.
have ha0 : a!=0.
  apply/eqP=> he; move: hr; by rewrite -har he inner_norm0 ltxx.
have hu0 := @inner_normalize_square R V B hB a ha0.
apply/seteqP; split=> z hz.
- exact (compact_enclosing_radius_contains (0 : inner_metric_space hB) S z hz).
- have hzn : inner_norm hB z<=r.
    by move: hz; rewrite /metric_closed_ball /= inner_metric_distanceE sub0r inner_normN.
  case: (eqVneq z 0)=> [hz0|hz0].
  + have ht0 : `|0 : R|<=r by rewrite normr0; exact: ltW hr.
    have hh := steiner_minimal_radius_radial_segment hX hC hS (ltW hr) hmin hb hu0 ht0.
    by rewrite scale0r -hz0 in hh.
  + have huz := @inner_normalize_square R V B hB z hz0.
    have ht : `|inner_norm hB z|<=r by rewrite ger0_norm ?inner_norm_nonnegative.
    have hh := steiner_minimal_radius_radial_segment hX hC hS (ltW hr) hmin hb huz ht.
    by rewrite inner_normalizeK in hh.
Qed.
