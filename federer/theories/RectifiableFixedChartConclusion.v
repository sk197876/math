(** Federer (1969), 3.2.19, p. 256: the complete fixed-lambda
    conclusions on W, before taking lambda down to one.
    All chart-point hypotheses are discharged using 3.2.18. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction
  LipschitzUP RectifiableSetUP RectifiableCompactChartsUP RectifiableCompactCharts
  RectifiableDifferentialChartUP RectifiableChartDensityDifferential
  RectifiableTangentPlaneUP EuclideanLinearRangePlane GrassmannSubspaces
  MeasureApproximateDifferentialUP MeasureApproximateTangentUP
  MeasureUP MeasureBasic MeasureRestriction MeasureAlmostUP MeasureAlmostBasic
  MeasureAlmostOnCover HausdorffMeasure MetricDensities.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [rectifiable_fixed_chart_conclusion]: the last three
    displays of the proof of Federer 3.2.19, p. 256, for
    one fixed lambda>1. The complete chart lemma supplies the countable
    cover; each pointwise approximate differential has exactly the tangent
    plane as domain. The upper density one bound is separate. *)
Theorem rectifiable_fixed_chart_conclusion (R : realType) m n k
    (lambda : R) (W : set (R_n R n)) (F : R_n R n -> R_n R k) :
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) m W ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  1<lambda ->
  @is_metric_lipschitz R (inner_metric_space (@euclidean_inner_productP R n))
    (inner_metric_space (@euclidean_inner_productP R k)) setT F ->
  let mu := @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m in
  measure_almost_everywhere_on mu W [set w |
    (((lambda^+(m+m))^-1)%R%:E<=lower_metric_density m (measure_restrict mu W) w)%E /\
    is_m_dimensional_approximate_tangent m (measure_restrict mu W) w /\
    measure_approximately_differentiable_at (inner_norm (@euclidean_inner_productP R k))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) (measure_restrict mu W) m
      (partial_function_source_restrict W (partial_function_total F)) w].
Proof.
move=> hRect hW hLam hF mu.
have hm := @hausdorff_measure_is_measure R (inner_metric_space (@euclidean_inner_productP R n)) m.
have [K [psi hCover]] := federer_3_2_18 hRect hW hLam.
apply: (@measure_almost_on_countable_cover R
  [the choiceType of inner_metric_space (@euclidean_inner_productP R n)] nat
  mu W setT (fun i=>psi i @` K i) _ hm (countableP _) hCover.2.2).
move=> i _.
have hLocal := rectifiable_chart_density_differential hLam (hCover.1 i).1
  (hCover.1 i).2 hW hRect.2 hF.
apply: (measure_null_subset hm _ hLocal)=> w [hw hn].
split; first exact hw.
move=> [hLow hPoint]; apply: hn; split; first exact hLow.
have [a [D [H [d [ha [hVal [hInj [hD [hH [hCone [hApprox hId]]]]]]]]]]] := hPoint.
have [P hPlane] := euclidean_injective_range_plane hInj.
split; last exact hApprox.1.
exists P; by rewrite hCone hPlane.
Qed.
