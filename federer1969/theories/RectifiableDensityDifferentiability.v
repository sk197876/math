(** Federer (1969), 3.2.19, p. 256: density one, an
    m-dimensional approximate tangent plane, and approximate differentiability
    almost everywhere on a measurable finite-measure rectifiable set.
    This file proves the globally extended-map form used in the proof. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction
  LipschitzUP RectifiableSetUP RectifiableTangentPlaneUP RectifiableFixedChartConclusion
  ReciprocalNearOnePowerBound MeasureApproximateDifferentialUP
  MeasureUP MeasureRestriction MeasureAlmostUP MeasureAlmostBasic HausdorffMeasure
  HausdorffRestrictedDensity MetricDensities.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [rectifiable_density_and_differentiability_global]: the
    whole conclusion of Federer 3.2.19, p. 256, after the
    proof's initial global Lipschitz extension F. Apply the fixed-lambda
    argument for lambda=1+1/(k+1), combine the countable exceptional sets,
    and force both metric densities to one. No extra rank or positive
    dimension premise is imposed. *)
Theorem rectifiable_density_and_differentiability_global (R : realType) m n k
    (W : set (R_n R n)) (F : R_n R n -> R_n R k) :
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  @is_metric_lipschitz R (inner_metric_space (@euclidean_inner_productP R n))
    (inner_metric_space (@euclidean_inner_productP R k)) setT F ->
  let mu := @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m in
  measure_almost_everywhere_on mu W [set w |
    partial_function_graph (metric_density m (measure_restrict mu W)) w 1%E /\
    is_m_dimensional_approximate_tangent m (measure_restrict mu W) w /\
    measure_approximately_differentiable_at (inner_norm (@euclidean_inner_productP R k))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) (measure_restrict mu W) m
      (partial_function_source_restrict W (partial_function_total F)) w].
Proof.
move=> hRect hW hF mu.
have hm := @hausdorff_measure_is_measure R (inner_metric_space (@euclidean_inner_productP R n)) m.
pose lam (j : nat) := (1+((j.+1)%:R : R)^-1).
pose Q (j : nat) := [set w : R_n R n |
  (((lam j)^+(m+m))^-1)%R%:E<=lower_metric_density m (measure_restrict mu W) w]%E.
pose T := [set w : R_n R n |
  is_m_dimensional_approximate_tangent m (measure_restrict mu W) w /\
  measure_approximately_differentiable_at (inner_norm (@euclidean_inner_productP R k))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) (measure_restrict mu W) m
    (partial_function_source_restrict W (partial_function_total F)) w].
have hLam j : 1<lam j by rewrite /lam ltrDl invr_gt0 ltr0n.
have hEach j : measure_almost_everywhere mu [set w | W w -> (Q j `&` T) w].
  apply: (@measure_almost_everywhere_on_implication R
    [the choiceType of inner_metric_space (@euclidean_inner_productP R n)] mu W (Q j `&` T)).1.
  exact: (rectifiable_fixed_chart_conclusion hRect hW (hLam j) hF).
have hAll := @measure_almost_everywhere_countable R
  [the choiceType of inner_metric_space (@euclidean_inner_productP R n)] nat mu hm
  setT (fun j=>[set w | W w -> (Q j `&` T) w]) (countableP _) (fun j _=>hEach j).
have hUpper := @finite_hausdorff_restricted_upper_density R
  [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] m W hRect.2.
have hBoth := measure_almost_everywhere_and hm hAll hUpper.
apply: (@measure_almost_everywhere_on_implication R
  [the choiceType of inner_metric_space (@euclidean_inner_productP R n)] mu W _).2.
apply: (measure_almost_everywhere_mono hm _ hBoth)=> w [hEvery hUp] hw.
have hOne : (1<=lower_metric_density m (measure_restrict mu W) w)%E.
  apply: (@reciprocal_near_one_power_forces_one R (m+m)
    (lower_metric_density m (measure_restrict mu W) w))=> j.
  exact: (hEvery j I hw).1.
have hOrder := metric_densities_ordered m (measure_restrict mu W) w.
have hLower : lower_metric_density m (measure_restrict mu W) w= 1%E.
  apply/eqP; rewrite eq_le hOne andbT; exact: le_trans hOrder hUp.
have hUpperEq : upper_metric_density m (measure_restrict mu W) w= 1%E.
  apply/eqP; rewrite eq_le hUp /=; exact: le_trans hOne hOrder.
split; [by split|exact: (hEvery 0%N I hw).2].
Qed.
