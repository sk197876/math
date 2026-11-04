(** Federer (1969), 3.2.46, p. 281: the actual tensor-speed
    integral of a Lipschitz curve on a compact interval is finite.
    Measurability and the derivative bound are proved, rather than
    included among admissibility hypotheses. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerMetric HilbertFormCompactness RealMetricBackground
  ExtendedRealOrderTopology LipschitzUP LipschitzBasic NormMetricScaleContinuity
  NormedCurveDerivativeUP NormedDerivativeBounds EuclideanCurveDifferentiability
  LipschitzCurveAbsoluteContinuity RiemannianTensorUP RiemannianCurveCost
  RiemannianCurveSpeedMeasurable RiemannianCurveUniformBound
  PartialFunctionUP PartialZeroExtension CharacteristicFunctionUP CharacteristicFunctionSealed
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableZeroExtension
  MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness MeasureSubsetIntegral
  BoundedSubsetSummability BorelRegularMeasureUP TopologicalBorel
  LebesgueScalarMeasure IntervalBumpFunctions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_global_curve_finite_integral]: the
    numbers in the distance infimum of Federer 3.2.46, p. 281,
    are genuine finite integrals. This supporting representative
    version retains zero Lipschitz bounds, degenerate intervals,
    all natural dimensions and the actual partial derivative graph. *)
Theorem riemannian_global_curve_finite_integral (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g)
    (C : real_line_metric R -> inner_metric_space (@euclidean_inner_productP R n))
    (L a b : R) :
  @is_metric_lipschitz_bound R [the metricType R of real_line_metric R]
    [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] setT C L ->
  (forall t, A (C t)) -> a <= b ->
  is_measure_subset_integral (@lebesgue_scalar_measure R) `[a,b]
    (riemannian_curve_speed g C) (riemannian_curve_cost g C a b) /\
  (riemannian_curve_cost g C a b < +oo)%E.
Proof.
move=> hBound hA hab.
pose mu := @lebesgue_scalar_measure R.
pose hm := lebesgue_scalar_is_measure R.
have hLip := metric_lipschitz_of_bound hBound.
have hCont : continuous C.
  apply: (@metric_fixed_lipschitz_continuous R _ _ C L hBound.1).
  by move=> t u; exact: hBound.2 t u Logic.I Logic.I.
have [M [hM hSpeed]] := riemannian_curve_uniform_speed_bound hg a b hCont hA.
have hAC := metric_lipschitz_curve_locally_absolute_continuous hBound.
have hAE := euclidean_absolute_continuous_derivative_almost hAC.
have hInterval : measure_measurable mu (`[a,b] : set (real_line_metric R)).
  have hClosed : @closed [the topologicalType of real_line_metric R] `[a,b].
    exact: segment_closed_real.
  exact (@borel_regular_borel_measurable R
    [the topologicalType of real_line_metric R] mu hm
    (lebesgue_scalar_borel_regular R) `[a,b] (closed_borel_set hClosed)).
have hFinite : (mu (`[a,b] : set (real_line_metric R)) < +oo)%E.
  by rewrite /mu lebesgue_scalar_segment // ltry.
pose F := partial_function_zero_extension (0 : extended_real_line R)
  `[a,b] (riemannian_curve_speed g C).
pose chi := @CharacteristicFunction.value R (real_line_metric R) `[a,b].
pose hChi := @CharacteristicFunction.laws R (real_line_metric R) `[a,b].
have hSummable : is_measure_summable mu F.
  apply: (@bounded_supported_partial_summable R [the choiceType of real_line_metric R]
    mu F `[a,b] chi (M*L) hm hInterval hFinite hChi
    (mulr_ge0 (ltW hM) hBound.1)).
  - exact (@measurable_zero_extension R [the choiceType of real_line_metric R]
      (extended_real_line R) mu hm 0 `[a,b] (riemannian_curve_speed g C)
      hInterval (@riemannian_curve_speed_measurable R n A g hg C hLip hA)).
  - apply: (@measure_almost_everywhere_mono R _ mu hm _ _ _ hAE)=> t [v hv].
    case: (pselect ((`[a,b] : set (real_line_metric R)) t))=> ht.
    + exists (riemannian_tensor_speed g (C t) v); split.
      * apply/partial_function_zero_extension_graph; left; split=> //.
        exists v; by split.
      * rewrite /chi (characteristic_on_set hChi ht) mulr1
          (ger0_norm (riemannian_tensor_speed_nonnegative g (C t) v)).
        have hV : inner_norm (@euclidean_inner_productP R n) v <= L.
          apply: (normed_curve_derivative_lipschitz_bound
            (inner_norm_real_norm (@euclidean_inner_productP R n)) _ hv).
          move=> u w; exact: hBound.2 u w Logic.I Logic.I.
        have ht' : a <= t <= b by move: ht; rewrite /mkset in_itv /=.
        exact: le_trans (hSpeed t ht' v) (ler_wpM2l (ltW hM) hV).
    + exists 0; split.
      * apply/partial_function_zero_extension_graph; right; by split.
      * by rewrite /chi (characteristic_off_set hChi ht) normr0 mulr0.
have [c hIntegral] := hSummable.
have hCost : riemannian_curve_cost g C a b = c%:E.
  exact: measure_upper_integral_unique (measure_upper_integral_specification mu F) hIntegral.2.1.
split; rewrite hCost; last exact: ltry.
exact: hIntegral.
Qed.
