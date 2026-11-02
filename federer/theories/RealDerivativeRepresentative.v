(** Federer (1969), 2.9.24, p. 169: bounded convergence can be calculated
    using a total representative of g', then transferred back to the actual
    partial derivative integrand. The proof representative uses the already
    sealed total-extension law of 2.3.2, p. 73; no value off the derivative
    domain is part of the public specification. The local Federer erratum
    has no entry for this supporting representative. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  PartialFunctionExtensionUP PartialFunctionExtensionSealed RealCurveDerivativeUP
  RealCurveDerivativeIntegrands CurveArcLength RealBVMonotoneDecomposition
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasurableFunctionUP LebesgueScalarMeasure
  ContinuousDerivativeMeasurable SummableRealFunctionUP MeasureIntegralUP
  MeasureIntegralAlmostEquality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_derivative_representative]: supporting total
    proof representative for g' in Federer 2.9.24, p. 169,
    using the abstract total extension from 2.3.2, p. 73.
    The original partial derivative and its domain are unchanged. *)
Definition real_derivative_representative (R : realType) (g : R -> R) : R -> R :=
  @PartialFunctionExtension.value R R (real_curve_derivative g) 0.

(** Source for [real_derivative_representative_value]: supporting
    graph agreement for the representative in Federer 2.9.24,
    p. 169. Every actual derivative value is preserved exactly. *)
Lemma real_derivative_representative_value (R : realType) (g : R -> R) (x v : R) :
  has_real_curve_derivative g x v -> real_derivative_representative g x=v.
Proof. exact: (@PartialFunctionExtension.laws R R (real_curve_derivative g) 0 x v). Qed.

(** Source for [bv_real_derivative_representative_ae]: supporting
    almost-everywhere agreement of the proof representative with
    the actual derivative in Federer 2.9.24, p. 169, using
    the existence part of 2.9.19, pp. 163–164. *)
Lemma bv_real_derivative_representative_ae (R : realType) (g : R -> R) :
  curve_locally_finite_variation (g : R -> real_line_metric R) ->
  measure_almost_everywhere (@lebesgue_scalar_measure R)
    [set x | has_real_curve_derivative g x (real_derivative_representative g x)].
Proof.
move=> hg.
have hD := @real_bv_joint_derivatives_ae R g hg.
apply: (@measure_almost_everywhere_mono R (real_line_metric R) _
  (lebesgue_scalar_is_measure R) _ _ _ hD)=> x [v [_ [hv _]]].
change (has_real_curve_derivative g x (real_derivative_representative g x)).
by rewrite (real_derivative_representative_value hv).
Qed.

(** Source for [continuous_bv_derivative_representative_measurable]:
    supporting scalar measurability for bounded convergence in
    Federer 2.9.24, p. 169. The continuous retracted curve's
    quotients give the existing measurable-limit proof. The
    representative is only a proof tool, not a redefinition of g'. *)
Lemma continuous_bv_derivative_representative_measurable (R : realType) (g : R -> R) :
  curve_locally_finite_variation (g : R -> real_line_metric R) ->
  continuous (g : real_line_metric R -> real_line_metric R) ->
  is_measure_measurable_function (@lebesgue_scalar_measure R)
    (partial_function_total
      (real_derivative_representative g : real_line_metric R -> real_line_metric R)).
Proof.
move=> hg hc; exact: continuous_scalar_derivative_representative_measurable
  (lebesgue_scalar_is_measure R) (lebesgue_scalar_borel_regular R) hc
  (bv_real_derivative_representative_ae hg).
Qed.

(** Source for [real_derivative_representative_integral]: supporting
    integral invariance under the representative used for Federer
    2.9.24, p. 169, by the null-replacement law of 2.4.3(2),
    p. 81. Any actual derivative integral transfers with exactly
    its value; the measure can already be restricted to a cell. *)
Lemma real_derivative_representative_integral (R : realType)
    (mu : set (real_line_metric R) -> \bar R) (hm : is_measure mu)
    (g : R -> R) (a : \bar R) :
  measure_almost_everywhere mu
    [set x | has_real_curve_derivative g x (real_derivative_representative g x)] ->
  is_measure_integral mu (real_curve_derivative_integrand g) a ->
  is_measure_integral mu (real_total_integrand (real_derivative_representative g)) a.
Proof.
move=> hD hi; apply: (measure_integral_almost_equal hm hi).
apply: (@measure_almost_everywhere_mono R (real_line_metric R) mu hm _ _ _ hD)=> x hx.
exists (real_derivative_representative g x)%:E; split.
- apply/real_curve_derivative_integrand_graph; by exists (real_derivative_representative g x); split.
- by apply/real_total_integrand_graph.
Qed.
