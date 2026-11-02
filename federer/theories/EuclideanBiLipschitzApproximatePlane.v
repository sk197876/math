(** Federer (1969), 3.2.17, pp. 254–255:
    every vector in the image differential
    plane is an approximate tangent. This
    proof transfers full-density test sets through
    the local inverse mass comparison, using
    the intersection definition from 3.2.16. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  RealNormUP NormMetric HilbertFormCompactness NormDifferentialUP
  EuclideanLebesgueDimensions EuclideanHausdorffLebesgue PartialFunctionUP
  MeasureUP MeasureBasic MeasureRestriction MeasureSetDensity CenteredBallRelations
  MetricDensities MetricDensityZeroUnions EuclideanMetricZeroDensity
  EuclideanMetricDensityConverse EuclideanFullDensityTangent
  MetricBiLipschitzUP MetricBiLipschitzZeroPullback HausdorffMeasure
  TangentConeUP TangentConeBasic TangentDifferentialImage MeasureApproximateTangentUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_bilipschitz_range_approximate_tangent]:
    the reverse tangent-plane inclusion in
    Federer 3.2.17, pp. 254–255.
    The printed directional-cone comparison is
    expressed here by the equivalent full-density
    intersection test of 3.2.16. *)
Theorem euclidean_bilipschitz_range_approximate_tangent (R : realType) m n
    (K : set (R_n R m)) (psi : R_n R m -> R_n R n) (lambda : R) a
    (L : Hom (R_n R m) (R_n R n)) :
  @is_metric_bilipschitz_bound R
    (inner_metric_space (@euclidean_inner_productP R m))
    (inner_metric_space (@euclidean_inner_productP R n)) K psi lambda ->
  0<lambda -> K a ->
  has_norm_differential (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) setT psi a L ->
  partial_function_graph (measure_set_density (@euclidean_lebesgue_measure R m)
    (@centered_closed_ball_relation R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R m)]) (~` K)) a 0%E ->
  range L `<=` measure_approximate_tangent_cone
    (inner_norm_real_norm (@euclidean_inner_productP R n))
    (measure_restrict (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) m) (psi @` K)) m (psi a).
Proof.
move=> hB hLam ha hPsi hFull w [v _ <-] S hS.
pose X := inner_metric_space (@euclidean_inner_productP R m).
pose Y := inner_metric_space (@euclidean_inner_productP R n).
pose mu := @euclidean_lebesgue_measure R m.
have hm := euclidean_lebesgue_is_measure R m.
have hKzero := euclidean_relative_zero_metric_zero_density hFull.
have hPull := @metric_bilipschitz_zero_density_pullback R X Y K psi lambda m a (~` S)
  hB hLam ha hS.
have hHL : @hausdorff_measure R X m=mu.
  apply: funext=> A; exact: (euclidean_hausdorff_spherical_lebesgue A).1.
rewrite hHL in hPull.
pose A := K `&` (psi @^-1` S).
have hBad := @metric_restricted_density_zero_union R X m mu
  (~` K) (K `&` (psi @^-1` (~` S))) a hm hKzero hPull.
have hAzero : partial_function_graph (metric_density m (measure_restrict mu (~` A))) a 0%E.
  apply: (@metric_restricted_density_zero_subset R X m mu (~` A)
    ((~` K) `|` (K `&` (psi @^-1` (~` S)))) a hm _ hBad).
  move=> x hn; case: (pselect (K x))=> hx; last by left.
  right; split=> // hSx; apply: hn; by split.
have hAold := euclidean_metric_zero_relative_zero_density hAzero.
have hATan := euclidean_full_density_tangent hAold.
have hv : norm_tangent_cone (inner_norm (@euclidean_inner_productP R m)) A a v.
  by rewrite hATan.
have himg := @norm_differential_tangent_image R (R_n R m) (R_n R n)
  (inner_norm (@euclidean_inner_productP R m)) (inner_norm (@euclidean_inner_productP R n))
  (inner_norm_real_norm (@euclidean_inner_productP R m))
  (inner_norm_real_norm (@euclidean_inner_productP R n)) setT A psi a L hPsi v hv.
apply: (@norm_tangent_mono R (R_n R n) (inner_norm (@euclidean_inner_productP R n))
  (psi @` (A `&` setT)) S (psi a) _ (L v) himg).
by move=> y [x [[_ hx] _] <-].
Qed.
