(** Federer (1969), 4.1.1, p. 346: the
    integral pairing of every actual smooth test
    is finite. On D_K its value is bounded
    by nu^0_K times the integral of the dual
    norm on the same K. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric RealMetricBackground NormRegularity
  ContinuousMultilinearSealed ContinuousDualUP VectorDaniellHypotheses
  OpenFamilyTopologyMathcomp WeakEvaluationTopologyUP WeakEvaluationMeasurableCoordinates
  PartialFunctionBasic MeasureUP MeasurableFunctionUP MeasureIntegralUP SummableRealFunctionUP
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothFunctionSupport
  SmoothDerivativeSeminormUP SmoothFunctionTopology SmoothTestSpaces SmoothTestEvaluation
  SmoothCompactTestMeasurable IntegrableCompactDualPairing DistributionIntegralFieldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section IntegralTestBound.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable YD:lmodType R.
Variable ed:Hom YD (Hom Y R^o).
Variable DN:YD->R.
Hypothesis hYD:is_continuous_dual hNY ed DN.
Hypothesis hSep:is_separable_normed_space hNY.
Variable O:set (set YD).
Hypothesis hO:is_weak_evaluation_topology (fun a y=>ed a y) O.
Variable mu:set X->\bar R.
Hypothesis hm:is_measure mu.
Hypothesis hOpen:forall A:set X,@open (real_norm_metric_space hNX) A ->measure_measurable mu A.
Variable xi:X->YD.
Hypothesis hXi:is_measure_measurable_function mu
  (partial_function_total (fun x=>(xi x:open_family_topological_space hO.1))).
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY (fun _=>True) ev.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY (fun _=>True) E ev D.
Local Notation DT := (smooth_test_space hE).
Local Notation inc := (smooth_test_inclusion hE).
Local Notation value := (smooth_test_value hE).
Local Notation support := (@smooth_function_support R X Y NX hNX (fun _=>True) E ev).
Local Notation nu := (smooth_function_derivative_seminorm hD).

(** Source for [distribution_integral_test_bound]: the
    actual pairing integral is finite and has
    its original order-zero local bound, supporting
    the distribution assertion in Federer 4.1.1,
    p. 346. *)
Theorem distribution_integral_test_bound (K:smooth_compact_set hNX (fun _=>True)) b f:
  support (inc f) `<=` smooth_compact_carrier K ->
  is_measure_integral mu (real_total_integrand
    (fun x=>if pselect (smooth_compact_carrier K x) then DN (xi x) else 0)) b%:E ->
  exists c:R,is_measure_integral mu (real_total_integrand (fun x=>ed (xi x) (value f x))) c%:E /\
    `|c|<=nu K 0%N (inc f)*b.
Proof.
move=>hSupport hLocal.
have hCoord y:=@weak_evaluation_measurable_coordinates R X Y YD (fun a y=>ed a y) O hO mu hm xi hXi y.
apply:(@integrable_compact_dual_pairing R X Y NY hNY YD ed DN hYD mu hm hSep xi hCoord
  (smooth_compact_carrier K) (value f) (nu K 0%N (inc f)) b).
- exact:smooth_compact_set_measurable hOpen K.
- exact (@smooth_test_value_measurable R X Y NX NY hNX hNY mu hm hOpen E ev hE f).
- move=>x hx; exact:((smooth_function_compact_support_iff hE K (inc f)).1 hSupport x hx).
- exact:smooth_derivative_seminorm_nonnegative (smooth_function_derivative_seminorm_laws hD K 0%N) (inc f).
- move=>x hx; exact (@smooth_test_zeroth_seminorm_value_bound R X Y NX NY hNX hNY E ev hE D hD f K x hx).
- exact hLocal.
Qed.
End IntegralTestBound.
