(** Federer (1969), 3.2.46, p. 281: every actual admissible
    compact-interval Lipschitz curve contributes a genuine finite
    integral to the distance infimum. A constant extension beyond
    the endpoints is used only to prove this existence assertion. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerMetric RealMetricBackground ExtendedRealOrderTopology
  LipschitzUP LipschitzIntervalRetraction LipschitzCurveAbsoluteContinuity
  StieltjesSubstitution RiemannianTensorUP RiemannianCurveCost
  RiemannianCurveFiniteIntegral RiemannianCurveIntervalAgreement
  MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness
  MeasureSubsetIntegral SubsetIntegralAlmostAgreement LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [riemannian_admissible_curve_finite_integral]:
    the defining integral in Federer 3.2.46, p. 281, exists and
    is finite for every curve specified there. Only the printed
    interval Lipschitz hypothesis and the tensor laws are used;
    derivatives at the endpoints are not required. *)
Theorem riemannian_admissible_curve_finite_integral (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) x y
    (C : real_line_metric R -> inner_metric_space (@euclidean_inner_productP R n)) a b :
  is_riemannian_admissible_curve A x y C a b ->
  is_measure_subset_integral (@lebesgue_scalar_measure R) `[a,b]
    (riemannian_curve_speed g C) (riemannian_curve_cost g C a b) /\
  (riemannian_curve_cost g C a b < +oo)%E.
Proof.
move=> [hab [[L [hL hBound]] [hImage [hStart hEnd]]]].
pose D := fun t : real_line_metric R => C (segment_retraction a b t).
have hD : @is_metric_lipschitz_bound R [the metricType R of real_line_metric R]
    [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] setT D L.
  exact (@metric_curve_retraction_lipschitz R
    [the metricType R of inner_metric_space (@euclidean_inner_productP R n)] C a b L hab hBound).
have hDImage : forall t, A (D t).
  exact: metric_curve_retraction_image hab hImage.
have hEq t : a <= t <= b -> C t = D t.
  move=> ht; exact: esym (metric_curve_retraction_agreement C ht).
have [hIntegral hFinite] := @riemannian_global_curve_finite_integral R n A g hg D L a b hD hDImage hab.
have hAgree := @riemannian_interval_speed_almost_agreement R n g C D a b
  hEq (metric_lipschitz_curve_locally_absolute_continuous hD).
have hOriginal := @subset_integral_almost_agreement R [the choiceType of real_line_metric R]
  (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R) `[a,b]
  (riemannian_curve_speed g D) (riemannian_curve_speed g C)
  (riemannian_curve_cost g D a b) hAgree hIntegral.
have hCost : riemannian_curve_cost g C a b = riemannian_curve_cost g D a b.
  exact: measure_upper_integral_unique (measure_upper_integral_specification _ _) hOriginal.2.1.
by split; rewrite hCost.
Qed.
