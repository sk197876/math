(** Federer (1969), 3.2.6, pp. 245–246: local absolute
    continuity supplies the actual curve derivative almost everywhere.
    This finite-dimensional specialization uses the proved 2.9.22
    theorem through its abstract norm and dual interfaces. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness NormMetric EuclideanOwnNormCompleteness FiniteNormCurveDifferentiability
  LocallyAbsolutelyContinuousCurve NormedCurveDerivativeUP MeasureAlmostUP LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [euclidean_absolute_continuous_derivative_almost]:
    derivative existence used in Federer 3.2.6, p. 246.
    Every finite target dimension, including the singleton target,
    is covered. No value is assigned where the derivative is absent. *)
Theorem euclidean_absolute_continuous_derivative_almost (R:realType) n
    (f:R->inner_metric_space (@euclidean_inner_productP R n)):
  is_locally_absolutely_continuous_curve f ->
  measure_almost_everywhere (@lebesgue_scalar_measure R)
    [set x|exists v:R_n R n,has_normed_curve_derivative
      (inner_norm (@euclidean_inner_productP R n)) f x v].
Proof.
move=>hAC.
pose hN:=inner_norm_real_norm (@euclidean_inner_productP R n).
have hACN:is_locally_absolutely_continuous_curve (fun x=>(f x:real_norm_metric_space hN)):=hAC.
exact (@finite_norm_bv_curve_derivative_almost R (R_n R n)
  (inner_norm (@euclidean_inner_productP R n)) hN n
  (@coordinate_basis R n) (@coordinate_basisP R n) f
  (@euclidean_own_norm_complete R n)
  (locally_absolutely_continuous_curve_finite_variation hACN)).
Qed.
