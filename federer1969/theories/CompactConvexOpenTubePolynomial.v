(** Federer (1969), 3.2.38, p. 275: apply the complete
    Steiner polynomial to the actual compact convex affine image. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric InnerConvex EuclideanLebesgueDimensions
  MetricOpenThickening MetricOpenThickeningClosure CompactSetDistanceProfile CompactMetricBounded
  SteinerTubePolynomial ConvexSteinerTubeFormula.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_convex_open_tube_polynomial]: supporting the
    first display on p. 275 of Federer 3.2.38, using 3.2.35.
    This uses the full j=0,...,n polynomial. The printed display's
    omission of j=0 is false for a constant affine map; the
    separately checked actual line-point counterexample certifies the
    correction. Compactness and nonemptiness discharge the distance
    laws locally, including ambient dimension zero. *)
Lemma compact_convex_open_tube_polynomial (R:realType) n
    (S:set (inner_metric_space (@euclidean_inner_productP R n))) (r:R):
  compact S ->S!=set0 ->is_inner_convex S ->0<r ->
  @euclidean_lebesgue_measure R n (metric_open_thickening S r)=steiner_tube_polynomial S r.
Proof.
move=>hCompact hNonempty hConvex hr.
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose C:compact_metric_set X:=exist _ S (mem_set (conj hCompact hNonempty)).
have hD:=compact_set_distance_profile_specification C.
have hBound:=compact_metric_diameter_finite C.
rewrite (@metric_open_thickening_distance R X S (compact_set_distance_profile C) r hD).
exact:(@convex_steiner_tube_formula R n S (compact_set_distance_profile C)
  hNonempty hConvex hBound hD r hr).
Qed.
