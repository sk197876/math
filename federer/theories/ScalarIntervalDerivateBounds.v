(** Federer (1969), 2.9.19, p. 164, the first two-sided mass estimate in the
    monotone case. The interval length is the actual positive finite scalar
    Lebesgue denominator. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground PartialFunctionUP MeasureDerivates LebesgueScalarMeasure
  ScalarIntervalDerivationContext MetricDiameter MetricDiameterReal CoveringFiniteLimitBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [scalar_interval_derivate_mass_bounds]: direct small-interval
    estimate in the first proof paragraph of Federer 2.9.19, p. 164. A
    finite derivate lambda bounds psi([a,b]) between (lambda-e)(b-a) and
    (lambda+e)(b-a) whenever a<=x<=b and the positive interval length is
    small. The proof only needs the actual derivate graph; no extra
    numerator regularity hypothesis is added. *)
Lemma scalar_interval_derivate_mass_bounds (R : realType)
    (psi : set (real_line_metric R) -> \bar R) (x : real_line_metric R) (lambda e : R) :
  partial_function_graph
    (measure_derivate psi (@lebesgue_scalar_measure R) (@scalar_nondegenerate_interval_relation R)) x lambda%:E ->
  0<e -> exists d : R, 0<d /\ forall a b : R,
    a<=x<=b -> 0<b-a<d ->
    (((lambda-e)*(b-a))%:E<=psi `[a,b])%E /\
    (psi `[a,b]<=((lambda+e)*(b-a))%:E)%E.
Proof.
move=> hD he.
have [d [hd hb]] := @covering_finite_limit_small_values R
  [the metricType R of real_line_metric R] (@scalar_nondegenerate_interval_relation R)
  (measure_ratio_function psi (@lebesgue_scalar_measure R)) x lambda e hD he.
exists d; split=> // a b haxb /andP [hpos hwidth].
have hab : a<b by rewrite -subr_gt0.
have hrel : scalar_nondegenerate_interval_relation x `[a,b].
  by exists a,b; split=> //; split.
have hdiam : (@extended_metric_diameter R [the metricType R of real_line_metric R] `[a,b]<d%:E)%E.
  by rewrite (@extended_metric_diameter_segment R a b (ltW hab)) lte_fin.
have hden : lebesgue_scalar_measure `[a,b]=(b-a)%:E.
  exact (@lebesgue_scalar_segment R a b (ltW hab)).
have hdp : (0<lebesgue_scalar_measure `[a,b])%E by rewrite hden lte_fin.
have hdf : lebesgue_scalar_measure `[a,b] \is a fin_num by rewrite hden.
have hq := @measure_ratio_positive_finite_denominator R (real_line_metric R) psi
  (@lebesgue_scalar_measure R) `[a,b] hdp hdf.
have [hl hu] := hb `[a,b] _ hrel hdiam hq.
split; apply: ltW.
- by move: hl; rewrite hden inver (gt_eqF hpos) lte_pdivlMr // -EFinM.
- by move: hu; rewrite hden inver (gt_eqF hpos) lte_pdivrMr // -EFinM.
Qed.
