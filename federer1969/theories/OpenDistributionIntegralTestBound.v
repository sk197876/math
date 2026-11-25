(** Federer (1969), 4.1.7, pp. 355–358: the
    original local mass-integrability bound on an
    arbitrary open U. Reuse the compact pairing
    theorem of 4.1.1, p. 346, on U itself,
    with its original relative topology and measure. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric RealMetricBackground ContinuousDualUP
  ContinuousMultilinearSealed VectorDaniellHypotheses OpenFamilyTopologyMathcomp WeakEvaluationTopologyUP
  WeakEvaluationMeasurableCoordinates PartialFunctionBasic MeasureUP RadonMeasureUP RadonBorelRegularity
  MeasurableFunctionUP MeasureIntegralUP SummableRealFunctionUP IsotropyGroupTopology
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothFunctionSupport
  SmoothTestSpaces SmoothTestEvaluation SmoothFunctionSeminormFamily SmoothFunctionTopology
  SmoothDerivativeSeminormUP DistributionVariationDomain DistributionSubspaceTestValues
  CompactContinuousVectorMeasurable IntegrableCompactDualPairing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section OpenDistributionIntegralTestBound.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypotheses (hNX:is_real_norm NX) (hNY:is_real_norm NY).
Variable U:set X.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Variable D:forall j,X->Hom E (@ContinuousMultilinear.space R j X Y NX NY hNX hNY).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.
Local Notation XT := (real_norm_metric_space hNX).
Local Notation UT := (set_type (U:set XT)).
Local Notation DT := (smooth_test_space hE).
Local Notation inc := (smooth_test_inclusion hE).
Local Notation values := (smooth_test_values_hom hE).
Local Notation dvalues := (@distribution_domain_values R XT U Y DT values).
Local Notation nu := (smooth_function_derivative_seminorm hD).
Variable YD:lmodType R.
Variable ed:Hom YD (Hom Y R^o).
Variable DN:YD->R.
Hypothesis hYD:is_continuous_dual hNY ed DN.
Hypothesis hSep:is_separable_normed_space hNY.
Variable O:set (set YD).
Hypothesis hO:is_weak_evaluation_topology (fun a y=>ed a y) O.
Variable mu:set UT->\bar R.
Hypothesis hm:is_measure mu.
Hypothesis hr:is_radon_measure mu.
Variable xi:UT->YD.
Hypothesis hXi:is_measure_measurable_function mu
  (partial_function_total (fun x=>(xi x:open_family_topological_space hO.1))).

(** Source for [open_distribution_test_zeroth_bound]:
    the original zeroth seminorm bounds the actual
    values on K inside U, supporting the original
    density currents of Federer 4.1.7, p. 356. *)
Lemma open_distribution_test_zeroth_bound f (K:smooth_compact_set hNX U) x:
  smooth_compact_carrier K x->NY (smooth_test_value hE f x)<=nu K 0%N (inc f).
Proof.
move=>hx.
have hBound:=smooth_derivative_seminorm_bound (smooth_function_derivative_seminorm_laws hD K 0%N)
  (inc f) (leqnn 0%N) hx.
rewrite (@smooth_derivative_zero_norm R X Y NX NY hNX hNY U E ev D hD (inc f) x
  (smooth_compact_in_domain K x hx)) in hBound;exact:hBound.
Qed.

(** Source for [open_distribution_integral_test_bound]:
    the actual pairing integral over U is finite
    and bounded by nu^0_K times the compact
    density-norm integral, supporting Federer 4.1.7,
    pp. 356–358. No extension across the boundary
    of U is required or assumed. *)
Theorem open_distribution_integral_test_bound (K:smooth_compact_set hNX U) b f:
  @smooth_function_support R X Y NX hNX U E ev (inc f) `<=` smooth_compact_carrier K ->
  is_measure_integral mu (real_total_integrand
    (fun x:UT=>if pselect (smooth_compact_carrier K (set_val x)) then DN (xi x) else 0)) b%:E ->
  exists c:R,is_measure_integral mu (real_total_integrand
    (fun x=>ed (xi x) (dvalues f x))) c%:E /\`|c|<=nu K 0%N (inc f)*b.
Proof.
move=>hSupport hLocal.
have hCoord y:=@weak_evaluation_measurable_coordinates R UT Y YD (fun a y=>ed a y) O hO
  mu hm xi hXi y.
pose S:set UT:=set_val @^-1` smooth_compact_carrier K.
have hCompact:compact S:=@set_type_compact_preimage XT U (smooth_compact_carrier K)
  (smooth_compact_is_compact K) (smooth_compact_in_domain K).
apply:(@integrable_compact_dual_pairing R UT Y NY hNY YD ed DN hYD mu hm hSep xi hCoord
  S (dvalues f) (nu K 0%N (inc f)) b).
- exact:(@radon_compact_measurable R UT mu hm hr S hCompact).
- exact:(@compact_continuous_vector_measurable R UT Y NY hNY mu hm hr (dvalues f)
    (@smooth_test_original_continuous_field R X Y NX NY hNX hNY U E ev hE f)).
- move=>x hx;exact:((smooth_function_compact_support_iff hE K (inc f)).1 hSupport (set_val x) hx).
- exact:smooth_derivative_seminorm_nonnegative (smooth_function_derivative_seminorm_laws hD K 0%N) (inc f).
- move=>x hx;exact:(@open_distribution_test_zeroth_bound f K (set_val x) hx).
- exact:hLocal.
Qed.
End OpenDistributionIntegralTestBound.
