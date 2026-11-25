(** Federer (1969), 2.9.22, p. 167: the actual norm derivative is
    characterised by every continuous dual derivative. These graph and
    integral adapters support the extension of 2.9.20(4)=>(1), p. 166. They
    retain the two partial derivative domains and transfer actual scalar
    integrals only after the common norm-derivative conull set is proved. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric RealMetricBackground ContinuousDualUP
  NormedCurveDerivativeUP NormedDerivativeDualEvaluation RealCurveDerivativeIntegrands
  MeasureVectorIntegralUP MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureAlmostEquality
  MeasureIntegralUP MeasureIntegralAlmostEquality MeasureRestriction MeasureSubsetIntegral
  RestrictedIntegralIdentity PartialFunctionUP LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [normed_derivative_evaluation_almost_equal]: direct
    partial-integrand compatibility supporting Federer 2.9.22,
    p. 167, dual characterisation, and the extension of 2.9.20(1),
    p. 165. At every actual norm derivative point, evaluation
    and the scalar partial derivative have one common defined value. *)
Lemma normed_derivative_evaluation_almost_equal (R : realType) (E D : lmodType R)
    (N : E -> R) (hN : is_real_norm N)
    (ed : Hom D (Hom E R^o)) (DN : D -> R)
    (hD : is_continuous_dual hN ed DN) (g : R -> E) :
  measure_almost_everywhere (@lebesgue_scalar_measure R)
    [set x | exists v : E, has_normed_curve_derivative N g x v] -> forall alpha : D,
  measure_almost_equal (@lebesgue_scalar_measure R)
    (partial_functional_evaluation (normed_curve_derivative hN g) (hom_as_linear (ed alpha)))
    (real_curve_derivative_integrand (fun t => ed alpha (g t))).
Proof.
move=> he alpha.
apply: (@measure_almost_everywhere_mono R (real_line_metric R) (@lebesgue_scalar_measure R)
  (lebesgue_scalar_is_measure R) _ _ _ he)=> x [v hv].
exists (ed alpha v)%:E; split.
- exists v; split=> //; by rewrite hom_as_linearE.
- exists (ed alpha v); split=> //.
  exact (@normed_curve_derivative_dual_evaluation R E D N hN ed DN hD g x v hv alpha).
Qed.

(** Source for [normed_derivative_evaluation_restricted_integral]:
    supporting dual integral transfer in Federer 2.9.22,
    pp. 167–168, extending 2.9.20(4)=>(1), p. 166. Convert
    the scalar subset integral to the restricted measure, then
    replace it by evaluation of the exact norm derivative on the
    proved conull set. The restricting set must be measurable for
    this subset/restricted equivalence, as it is for book segments. *)
Lemma normed_derivative_evaluation_restricted_integral (R : realType) (E D : lmodType R)
    (N : E -> R) (hN : is_real_norm N)
    (ed : Hom D (Hom E R^o)) (DN : D -> R)
    (hD : is_continuous_dual hN ed DN) (g : R -> E)
    (A : set (real_line_metric R)) (alpha : D) (I : R) :
  measure_almost_everywhere (@lebesgue_scalar_measure R)
    [set x | exists v : E, has_normed_curve_derivative N g x v] ->
  measure_measurable (@lebesgue_scalar_measure R) A ->
  is_measure_subset_integral (@lebesgue_scalar_measure R) A
    (real_curve_derivative_integrand (fun t => ed alpha (g t))) I%:E ->
  is_measure_integral (measure_restrict (@lebesgue_scalar_measure R) A)
    (partial_functional_evaluation (normed_curve_derivative hN g) (hom_as_linear (ed alpha))) I%:E.
Proof.
move=> he hA hi; have hm := lebesgue_scalar_is_measure R.
have hEq := @normed_derivative_evaluation_almost_equal R E D N hN ed DN hD g he alpha.
have hEqA : measure_almost_equal (measure_restrict (@lebesgue_scalar_measure R) A)
    (partial_functional_evaluation (normed_curve_derivative hN g) (hom_as_linear (ed alpha)))
    (real_curve_derivative_integrand (fun t => ed alpha (g t))).
  apply: (@measure_null_subset R (real_line_metric R) (@lebesgue_scalar_measure R) hm _ _ _ hEq).
  by move=> x [_ hx].
have hiA := (@restricted_integral_zero_extension_iff R (real_line_metric R)
  (@lebesgue_scalar_measure R) hm A _ I%:E hA).2 hi.
exact (@measure_integral_almost_equal R (real_line_metric R)
  (measure_restrict (@lebesgue_scalar_measure R) A) (measure_restrict_is_measure hm A)
  _ _ I%:E hiA (measure_almost_equal_sym hEqA)).
Qed.
