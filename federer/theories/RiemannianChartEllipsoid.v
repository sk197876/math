(** Federer (1969), 3.2.46, p. 281: the local
    comparison ellipsoid contains an open neighbourhood of
    its centre in the actual rho topology. Continuity is
    proved through the original chart inclusion and linear L. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets topology num_normedtype pseudometric_normed_Zmodule normed_module.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanLinearMaps TopologicalProductMaps MetricPairDistance RealMetricBackground
  RiemannianTensorUP RiemannianMetricCarrier RiemannianChartReference.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports numFieldNormedType.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_chart_ellipsoid_open]: the open
    interior of the actual L-coordinate ellipsoid is a rho
    neighbourhood, supporting the localisation in 3.2.46,
    pp. 281–282. L need not be nonsingular for this fact. *)
Lemma riemannian_chart_ellipsoid_open (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g)
    (L : {linear R_n R n -> R_n R n}) o (r : R) :
  open [set x : riemannian_metric_space hg |
    inner_norm (@euclidean_inner_productP R n) (L (val x-o))<r].
Proof.
pose M := [the topologicalType of riemannian_metric_space hg].
pose E := [the metricType R of inner_metric_space (@euclidean_inner_productP R n)].
have hL : continuous (fun x : M=>(L (val x) : E)).
  move=> x; exact (continuous_comp (@riemannian_chart_inclusion_continuous R n A g hg x)
    (@euclidean_linear_continuous R n L (val x))).
have hPair : continuous (fun x : M=>(L (val x),L o) : E*E).
  apply: topological_pair_continuous; first exact hL; exact: cst_continuous.
have hGauge : continuous (fun x : M=>(inner_norm (@euclidean_inner_productP R n)
    (L (val x-o)) : real_line_metric R)).
  have hEq : (fun x : M=>(inner_norm (@euclidean_inner_productP R n)
      (L (val x-o)) : real_line_metric R)) =
      (fun x : M=>(mdist (L (val x) : E) (L o) : real_line_metric R)).
    apply: funext=> x; by rewrite inner_metric_distanceE -linearB.
  rewrite hEq=> x; exact (continuous_comp (hPair x)
    (@metric_pair_distance_continuous R E (L (val x),L o))).
exact (@open_comp M (real_line_metric R)
  (fun x : M=>(inner_norm (@euclidean_inner_productP R n) (L (val x-o)) : real_line_metric R))
  [set y : real_line_metric R | y<r] (fun x _=>hGauge x) (@open_lt R r)).
Qed.
