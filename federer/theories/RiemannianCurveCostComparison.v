(** Federer (1969), 3.2.46, p. 281: compare the genuine
    curve integrals by the pointwise tensor-speed inequalities.
    The original admissible curve and derivative graph are
    retained in both integrands. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerMetric RealMetricBackground ExtendedRealOrderTopology
  RiemannianTensorUP RiemannianCurveCost RiemannianAdmissibleIntegral
  PartialFunctionUP PartialZeroExtension PartialExtendedOrderLoci
  MeasureUpperIntegralScale MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasurableFunctionUP MeasureIntegralUP PartialSubsetIntegralComparison
  LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_curve_cost_positive_comparison]:
    integration of the local lambda-speed inequality in Federer
    3.2.46, p. 281. No derivative or integrability premise is
    added to the actual interval-only admissible curve. *)
Lemma riemannian_curve_cost_positive_comparison (R : realType) n A g h
    (hg : @is_continuous_riemannian_tensor R n A g)
    (hh : @is_continuous_riemannian_tensor R n A h) x y
    (C : real_line_metric R -> inner_metric_space (@euclidean_inner_productP R n)) a b c :
  is_riemannian_admissible_curve A x y C a b -> 0 < c ->
  (forall t, a <= t <= b -> forall v,
    riemannian_tensor_speed g (C t) v <= c*riemannian_tensor_speed h (C t) v) ->
  (riemannian_curve_cost g C a b <= c%:E*riemannian_curve_cost h C a b)%E.
Proof.
move=> hC hc hBound.
have hGIntegral := (riemannian_admissible_curve_finite_integral hg hC).1.
have hHIntegral := (riemannian_admissible_curve_finite_integral hh hC).1.
apply: (@subset_partial_integral_positive_comparison R [the choiceType of real_line_metric R]
  (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R) `[a,b]
  (riemannian_curve_speed g C) (riemannian_curve_speed h C) c
  (riemannian_curve_cost g C a b) (riemannian_curve_cost h C a b)
  hc hGIntegral hHIntegral).
apply: (measure_almost_everywhere_on_implication _ _ _).2.
apply: (measure_almost_everywhere_mono (lebesgue_scalar_is_measure R) _
  (measurable_function_domain hGIntegral.1)).
move=> t [z hz] ht.
have hRaw := (@partial_function_zero_extension_on (real_line_metric R)
  (extended_real_line R) 0 `[a,b] (riemannian_curve_speed g C) t z ht).1 hz.
have [v [hv hValue]] := hRaw.
exists (riemannian_tensor_speed g (C t) v)%:E,
  (c%:E*(riemannian_tensor_speed h (C t) v)%:E)%E; split.
- exists v; by split.
- split.
  + exists (riemannian_tensor_speed h (C t) v)%:E; split; last reflexivity.
    exists v; by split.
  + rewrite -EFinM lee_fin; apply: hBound.
    by move: ht; rewrite /mkset in_itv /=.
Qed.
