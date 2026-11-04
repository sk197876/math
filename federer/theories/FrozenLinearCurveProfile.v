(** Federer (1969), 3.2.46, p. 281: first-exit and
    last-return arguments use the actual continuous radius
    t |-> |L(C(t)-a)| of a Lipschitz representative. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerMetric RealMetricBackground LipschitzUP NormMetricScaleContinuity
  EuclideanLinearMaps MetricPairDistance TopologicalProductMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [frozen_linear_curve_profile_continuous]:
    continuity of the actual ellipsoid-radius profile used
    for the lower distance comparison in Federer 3.2.46,
    p. 281. No derivative of the radius is assumed. *)
Lemma frozen_linear_curve_profile_continuous (R : realType) n
    (L : {linear R_n R n -> R_n R n}) a
    (C : real_line_metric R -> inner_metric_space (@euclidean_inner_productP R n)) ell :
  @is_metric_lipschitz_bound R [the metricType R of real_line_metric R]
    [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] setT C ell ->
  continuous (fun t : real_line_metric R =>
    (inner_norm (@euclidean_inner_productP R n) (L (C t-a)) : real_line_metric R)).
Proof.
move=> hC.
pose E := inner_metric_space (@euclidean_inner_productP R n).
have hCont : continuous C.
  apply: (@metric_fixed_lipschitz_continuous R _ _ C ell hC.1).
  by move=> t u; exact: hC.2 t u Logic.I Logic.I.
have hPoint : continuous (fun t : real_line_metric R => (L (C t) : E)).
  move=> t; exact: continuous_comp (hCont t) (@euclidean_linear_continuous R n L (C t)).
have hConst : continuous (fun t : real_line_metric R => (L a : E)).
  by move=> t; exact: cvg_cst.
have hPair := topological_pair_continuous hPoint hConst.
have he : (fun t : real_line_metric R =>
      (inner_norm (@euclidean_inner_productP R n) (L (C t-a)) : real_line_metric R)) =
    (fun t : real_line_metric R => (mdist (L (C t) : E) (L a) : real_line_metric R)).
  by apply: funext=> t; rewrite inner_metric_distanceE linearB.
rewrite he; move=> t.
exact: continuous_comp (hPair t) (@metric_pair_distance_continuous R [the metricType R of E]
  (L (C t),L a)).
Qed.
