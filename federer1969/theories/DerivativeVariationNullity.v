(** Federer (1969), 2.9.22, p. 168: zero derivative almost everywhere on a
    set of zero derivative-integral mass. The measure is the sum of the
    continuous parts from 2.9.19, p. 165. Borel hulls allow an arbitrary
    null target set, without assuming its inverse image Lebesgue measurable.
    The zero-integral test is already derived from characteristic lower
    functions in the project. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology CurveArcLength StieltjesImageMeasures
  StieltjesDerivationClass ScalarIntervalDerivationContext MeasureDerivationContext
  ContinuousPartDecomposition ContinuousPartDecompositionUP BorelRegularMeasureUP
  BorelRegularMeasureAddition DerivativeVariationMeasure RealCurveDerivativeUP
  RealCurveDerivativeIntegrands LebesgueScalarMeasure MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureSubsetIntegral MeasureIntegralUP MeasureNonnegativeZero MeasurableFunctionUP
  PartialFunctionUP PartialFunctionBasic PartialZeroExtension PartialExtendedOrderLoci.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_derivative_variation_borel_regular]: supporting
    Borel hull for the weighted null-preimage conclusion of Federer
    2.9.22, p. 168. Each continuous part belongs to the class M
    by 2.9.2, p. 153; intersecting their Borel hulls proves regularity
    of their sum. No measurability of the test set is assumed. *)
Lemma real_derivative_variation_borel_regular (R : realType) (g : R -> R)
    (psip psim : set R -> \bar R) :
  curve_locally_finite_variation (g : R -> real_line_metric R) ->
  is_induced_measure_pair g psip psim ->
  @is_borel_regular_measure R [the topologicalType of real_line_metric R]
    (real_derivative_variation_measure psip psim).
Proof.
move=> hg hp.
have [hP hM] := @stieltjes_induced_pair_derivation_class R g psip psim hg hp.
have hL := derivation_context_measure (scalar_interval_derivation_context R).
have [B [hdP _]] := @measure_continuous_part_decomposition R [the metricType R of real_line_metric R]
  (@lebesgue_scalar_measure R) psip hL hP.
have [C [hdM _]] := @measure_continuous_part_decomposition R [the metricType R of real_line_metric R]
  (@lebesgue_scalar_measure R) psim hL hM.
have hcP := continuous_decomposition_class hdP.
have hcM := continuous_decomposition_class hdM.
exact: measure_binary_addition_borel_regular (derivation_measure_law hcP)
  (derivation_measure_law hcM) (derivation_measure_borel_regular hcP) (derivation_measure_borel_regular hcM).
Qed.

(** Source for [real_derivative_zero_on_variation_null]: direct
    zero-integral implication needed in Federer 2.9.22, p. 168.
    If the actual |g'| variation measure vanishes on A, then g'=0
    almost everywhere on A. A Borel null hull supplies the actual
    subset integral; positivity and the proved zero-integral test
    retain the genuine derivative domain, including exceptional points. *)
Theorem real_derivative_zero_on_variation_null (R : realType) (g : R -> R)
    (psip psim : set R -> \bar R) (A : set (real_line_metric R)) :
  curve_locally_finite_variation (g : R -> real_line_metric R) ->
  is_induced_measure_pair g psip psim ->
  real_derivative_variation_measure psip psim A=0%E ->
  measure_almost_everywhere (@lebesgue_scalar_measure R)
    [set x | A x -> has_real_curve_derivative g x 0].
Proof.
move=> hg hp hA0.
have [hn [hrep [hz hseg]]] := @real_derivative_variation_measure_laws R g psip psim hg hp.
have hr := @real_derivative_variation_borel_regular R g psip psim hg hp.
have [B [hAB [hB hmass]]] := borel_regular_cover hr A.
have hBm := @borel_regular_borel_measurable R [the topologicalType of real_line_metric R]
  (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R) (lebesgue_scalar_borel_regular R) B hB.
have hi := (hrep B hBm).2.
rewrite -hmass hA0 in hi.
pose f := partial_function_zero_extension (0%E : extended_real_line R) B
  (real_curve_absolute_derivative_integrand g).
have hNN : measure_almost_everywhere (@lebesgue_scalar_measure R) (partial_extended_nonnegative_locus f).
  apply: (@measure_almost_everywhere_mono R (real_line_metric R) (@lebesgue_scalar_measure R)
    (lebesgue_scalar_is_measure R) _ _ _ (measurable_function_domain hi.1))=> x [z hf].
  exists z; split=> //.
  have [[hx hz']|[_ hz']] := (partial_function_zero_extension_graph _ _ _ _ _).1 hf.
  - exact: real_curve_absolute_derivative_nonnegative hz'.
  - by rewrite -hz'.
have he := @nonnegative_integral_zero_almost_equal R (real_line_metric R)
  (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R) f hi hNN.
apply: (@measure_almost_everywhere_mono R (real_line_metric R) (@lebesgue_scalar_measure R)
  (lebesgue_scalar_is_measure R) _ _ _ he)=> x [z [hf hz0]] hx.
have hxB := hAB x hx.
have hfg : partial_function_graph (real_curve_absolute_derivative_integrand g) x z.
  by move: hf; rewrite /f partial_function_zero_extension_on.
have [v [hd heq]] := (real_curve_absolute_derivative_integrand_graph g x z).1 hfg.
have hv0 : v=0.
  have he0 : `|v|%:E=(0 : \bar R)%E by rewrite heq -(hz0 : 0%E=z).
  have heR : `|v|=0 by case: he0.
  by move: heR=> /eqP; rewrite normr_eq0=> /eqP.
by rewrite hv0 in hd.
Qed.
