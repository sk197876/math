(** Federer (1969), 3.2.46, p. 281: the curve length
    on a compact interval depends only on its original values
    there. The endpoints are discarded only by their proved
    scalar nullity; actual interior derivatives are preserved. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct
  InnerMetric RealMetricBackground LocallyAbsolutelyContinuousCurve
  RiemannianTensorUP RiemannianCurveCost RiemannianAdmissibleIntegral
  RiemannianCurveIntervalAgreement MeasureIntegralBounds MeasureIntegralUniqueness
  SubsetIntegralAlmostAgreement LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [riemannian_curve_interval_cost_agreement]:
    interval agreement preserves the genuine length integral
    used in Federer 3.2.46, p. 281. The representative's
    regularity supplies the actual common derivative domain. *)
Lemma riemannian_curve_interval_cost_agreement (R : realType) n A g
    (hg : @is_continuous_riemannian_tensor R n A g) x y u v
    (C D : real_line_metric R -> inner_metric_space (@euclidean_inner_productP R n)) a b :
  is_riemannian_admissible_curve A x y C a b ->
  is_riemannian_admissible_curve A u v D a b ->
  is_locally_absolutely_continuous_curve D ->
  (forall t, a <= t <= b -> C t = D t) ->
  riemannian_curve_cost g C a b = riemannian_curve_cost g D a b.
Proof.
move=> hC hD hAC hEq.
have hi := (riemannian_admissible_curve_finite_integral hg hD).1.
have hAgree := @riemannian_interval_speed_almost_agreement R n g C D a b hEq hAC.
have hOriginal := subset_integral_almost_agreement (lebesgue_scalar_is_measure R) hAgree hi.
exact: measure_upper_integral_unique (measure_upper_integral_specification _ _) hOriginal.2.1.
Qed.
