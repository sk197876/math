(** Federer (1969), 2.9.25, p. 169: combine the integral means of 2.9.8, p.
    156, with interval additivity to differentiate a primitive at an
    interior point. This local calculus step precedes the almost-everywhere
    application. No relevant local Federer erratum entry. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology ExtendedRealConventions
  PartialFunctionUP MeasureSubsetIntegral LebesgueScalarMeasure RealSegmentIntegralDifference
  MeasureMeanFunction CoveringRelationLimits CoveringFiniteLimitBounds MetricDiameter MetricDiameterReal
  ScalarIntervalDerivationContext RealCurveDerivativeUP RealIncrementDifferentiation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [integral_mean_limit_primitive_derivative_at]: supporting
    two-sided differentiation step in Federer 2.9.25, p. 169 At an interior
    point, all sufficiently short intervals containing the point lie inside
    the primitive's interval. No values or primitive identity outside the
    interval are used. *)
Theorem integral_mean_limit_primitive_derivative_at (R : realType)
    (f : partial_function (real_line_metric R) (extended_real_line R))
    (g : R -> R) (a b x c : R) : a<x -> x<b ->
  (forall t : R, a<=t -> t<=b ->
    is_measure_subset_integral (@lebesgue_scalar_measure R) `[a,t] f (g t)%:E) ->
  partial_function_graph
    (covering_relation_limit (@scalar_nondegenerate_interval_relation R)
      (measure_mean_function (@lebesgue_scalar_measure R) f)) x c%:E ->
  has_real_curve_derivative g x c.
Proof.
move=> hax hxb hF hlim.
apply: interval_increment_bounds_derivative=> e he.
have [d [hd hB]] := @covering_finite_limit_small_values R
  [the metricType R of real_line_metric R] (@scalar_nondegenerate_interval_relation R)
  (measure_mean_function (@lebesgue_scalar_measure R) f) x c e hlim he.
pose r := Num.min d (Num.min (x-a) (b-x)).
have hr : 0<r by rewrite /r !lt_min hd !subr_gt0 hax hxb.
exists r; split=> // u v /andP[hux hxv] /andP[hpos hsmall].
have hrd : r<=d by rewrite /r ge_min lexx.
have hrm : r<=Num.min (x-a) (b-x) by rewrite /r ge_min lexx orbT.
have hra : r<=x-a.
  apply: le_trans hrm _; by rewrite ge_min lexx.
have hrb : r<=b-x.
  apply: le_trans hrm _; by rewrite ge_min lexx orbT.
have hau : a<=u by lra.
have hvb : v<=b by lra.
have huv : u<=v by lra.
have hi := @lebesgue_segment_integral_finite_difference R f a u v (g u) (g v)
  hau huv (hF u hau (le_trans huv hvb)) (hF v (le_trans hau huv) hvb).
have hrel : scalar_nondegenerate_interval_relation x `[u,v].
  exists u,v; split; first by rewrite -subr_gt0.
  split=> //; exact/andP.
have hdiam : (@extended_metric_diameter R [the metricType R of real_line_metric R] `[u,v]<d%:E)%E.
  rewrite (extended_metric_diameter_segment huv) lte_fin.
  exact: lt_le_trans hsmall hrd.
have hmean : partial_function_graph (measure_mean_function (@lebesgue_scalar_measure R) f)
    `[u,v] ((g v-g u)/(v-u))%:E.
  exists (g v-g u)%:E; split=> //.
  rewrite (lebesgue_scalar_segment huv) /extended_divide.
  have hposE : (0<(v-u)%:E :> \bar R)%E by rewrite lte_fin.
  rewrite (gt_eqF hposE) /= inver (gt_eqF hpos) -EFinM; by [].
have [hlo hup] := hB `[u,v] _ hrel hdiam hmean.
have hlo' : c-e<(g v-g u)/(v-u) by move: hlo; rewrite lte_fin.
have hup' : (g v-g u)/(v-u)<c+e by move: hup; rewrite lte_fin.
split.
- apply: ltW; by move: hlo'; rewrite ltr_pdivlMr.
- apply: ltW; by move: hup'; rewrite ltr_pdivrMr.
Qed.
