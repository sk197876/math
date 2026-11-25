(** Federer (1969), 3.2.19, p. 256: on almost every point
    of a compact chart image, the lower W-density has the printed
    lambda bound and the actual differential gives the approximate tangent
    plane and the exact approximate-differential chain rule. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness NormDifferentialUP NormMetric
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction PartialFunctionPrecomposition
  RectifiableCompactChartsUP RectifiableCompactChartLaws RectifiableChartRegularParameters
  RectifiableDifferentialChartUP EuclideanParametrizedDensityTangent RelativeDifferentialUP
  MeasureApproximateTangentUP MeasureApproximateDifferentialUP
  RelativeMeasureApproximateDifferential RestrictedApproximateTangent TangentConeUP
  LipschitzUP MeasureUP MeasureBasic MeasureFiniteClosure MeasureRestriction
  MeasureAlmostUP MeasureAlmostBasic HausdorffMeasure HausdorffRestrictedDensity
  MetricDensities MetricDensityMonotonicity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [rectifiable_chart_density_differential]: all the
    fixed-lambda conclusions on psi_i(K_i) in the proof of Federer
    3.2.19, p. 256. The exceptional source sets are transported
    by 2.10.11; 2.10.19(4) gives zero density of the actual
    omitted set W minus the chart image. *)
Theorem rectifiable_chart_density_differential (R : realType) m n k
    (lambda : R) (W : set (R_n R n)) (K : set (R_n R m))
    (psi : R_n R m -> R_n R n) (F : R_n R n -> R_n R k) :
  1<lambda -> is_uniform_compact_rectifiable_chart lambda K psi ->
  psi @` K `<=` W ->
  measure_measurable (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m) W ->
  (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m W< +oo)%E ->
  @is_metric_lipschitz R (inner_metric_space (@euclidean_inner_productP R n))
    (inner_metric_space (@euclidean_inner_productP R k)) setT F ->
  measure_almost_everywhere_on
    (@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m)
    (psi @` K) [set w |
      (((lambda^+(m+m))^-1)%R%:E<=lower_metric_density m
        (measure_restrict (@hausdorff_measure R
          (inner_metric_space (@euclidean_inner_productP R n)) m) W) w)%E /\
      is_rectifiable_differential_chart_point W K psi F w].
Proof.
move=> hLam hChart hEW hW hFin hF.
pose Y := inner_metric_space (@euclidean_inner_productP R n).
pose NY := inner_norm (@euclidean_inner_productP R n).
pose hNY := inner_norm_real_norm (@euclidean_inner_productP R n).
pose mu := @hausdorff_measure R Y m.
pose E := psi @` K.
have hm := @hausdorff_measure_is_measure R Y m.
have hE : measure_measurable mu E.
  apply: (@rectifiable_chart_piece_measurable R m n lambda W E).
  split; first exact hEW; exists K,psi; by split.
have hOmit : measure_measurable mu (W `\` E) := measure_measurable_difference hm hW hE.
have hOmitFin : (mu (W `\` E)< +oo)%E.
  have hOmitW : W `\` E `<=` W by move=> x hx; exact hx.1.
  exact: (le_lt_trans (@measure_mono R Y mu hm (W `\` E) W hOmitW) hFin).
have hOff := @finite_hausdorff_off_set_density_zero R [the metricType R of Y] m
  (W `\` E) hOmit hOmitFin.
have hLamPos : 0<lambda := lt_trans ltr01 hLam.
have [A [hAK [hLoss hRegular]]] := rectifiable_chart_regular_parameters hLamPos hChart hF.
pose P : set Y := [set w | partial_function_graph (metric_density m (measure_restrict mu (W `\` E))) w 0%E].
have hBadOff : mu (E `\` P)=0%E.
  apply: (measure_null_subset hm _ hOff)=> w [hw hn].
  split=> //; by move=> [_ hwNot]; exact: hwNot hw.
have hBad := measure_null_union hm hLoss hBadOff.
apply: (measure_null_subset hm _ hBad)=> w [hw hNot].
case: (pselect ((psi @` A) w))=> hIn; last by left; split.
case: (pselect (P w))=> hP; last by right; split.
exfalso; apply: hNot.
have [a ha hEq] := hIn.
rewrite -hEq in hP.
rewrite -hEq.
have [hFull [[D [hPsi hInj]] [H hComp]]] := hRegular a ha.
have hka := hAK a ha.
have hB := uniform_compact_chart_bilipschitz hChart.
have hMain := @federer_3_2_17 R m n K psi lambda a D hB hLam hka hInj hPsi hFull.
have [hLow [_ [_ [hApprox [hTan hChain]]]]] := hMain.
have hCone : measure_approximate_tangent_cone hNY (measure_restrict mu W) m (psi a)=range D.
  have hZeroNorm : partial_function_graph (@metric_density R (real_norm_metric_space hNY) m
      (measure_restrict mu (W `\` E))) (psi a) 0%E := hP.
  have hTransfer := @restricted_approximate_tangent_equal R (R_n R n) NY hNY m mu E W
    (psi a) hm hEW hZeroNorm.
  exact: (eq_trans (esym hTransfer) (eq_trans hApprox hTan)).
have [d [hRel hIdentity]] := hChain k F H hComp.
have hConeTan : measure_approximate_tangent_cone hNY (measure_restrict mu W) m (psi a)=
    norm_tangent_cone NY E (psi a) by rewrite hCone hTan.
have hApproxD := @relative_differential_is_measure_approximate R (R_n R n) (R_n R k)
  NY (inner_norm (@euclidean_inner_productP R k)) hNY
  (inner_norm_real_norm (@euclidean_inner_productP R k)) mu m W E F (psi a) d
  hm hEW hP hConeTan hRel.
split.
- have hMeasureOrder (B : set Y) : (measure_restrict mu E B<=measure_restrict mu W B)%E.
    apply: (@measure_mono R Y mu hm (E `&` B) (W `&` B)).
    by move=> x [hx hb]; split; first exact: hEW x hx.
  have hLowerOrder := (@metric_densities_monotone R [the metricType R of Y] m
    (measure_restrict mu E) (measure_restrict mu W) (psi a) hMeasureOrder).1.
  exact: (le_trans hLow hLowerOrder).
- exists a,D,H,d; split; first exact hka.
  split; first reflexivity.
  split; first exact hInj.
  split; first exact hPsi.
  split; first exact hComp.
  split; first exact hCone.
  by split.
Qed.
