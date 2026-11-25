(** Federer (1969), 4.1.1, p. 346: actual
    finite integral values define a real linear
    functional on D. The proof uses the exact
    compact test estimate and the integral
    arithmetic already proved in Chapter 2. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric RealMetricBackground NormRegularity
  ContinuousMultilinearSealed ContinuousDualUP VectorDaniellHypotheses
  OpenFamilyTopologyMathcomp WeakEvaluationTopologyUP WeakEvaluationMeasurableCoordinates
  PartialFunctionBasic MeasureUP MeasurableFunctionUP MeasureIntegralUP SummableRealFunctionUP
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothFunctionSupport
  SmoothDerivativeSeminormUP SmoothFunctionTopology SmoothTestSpaces SmoothTestEvaluation
  SmoothCompactTestMeasurable IntegrableCompactDualPairing DistributionIntegralFieldUP
  DistributionIntegralTestBound RealIntegralLinearMapExistence SmoothFunctionSpaceLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section IntegralFunctionalExistence.
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

Hypothesis hLocal:forall K:smooth_compact_set hNX (fun _=>True),exists b:R,
  is_measure_integral mu (real_total_integrand
    (fun x=>if pselect (smooth_compact_carrier K x) then DN (xi x) else 0)) b%:E.

(** Source for [distribution_integral_pairing_finite]: every
    actual test pairing has a finite integral,
    supporting Federer 4.1.1, p. 346. *)
Theorem distribution_integral_pairing_finite f:
  exists c:R,is_measure_integral mu (real_total_integrand (fun x=>ed (xi x) (value f x))) c%:E.
Proof.
have [K hK]:=smooth_test_support_bound hE f.
have [b hb]:=hLocal K.
have [c [hc hBound]]:=@distribution_integral_test_bound R X Y NX NY hNX hNY YD ed DN hYD hSep O hO
  mu hm hOpen xi hXi E ev hE D hD K b f hK hb.
by exists c.
Qed.

(** Source for [distribution_integral_pairing_linear]: the
    actual integrand is linear in the test,
    supporting Federer 4.1.1, p. 346. *)
Lemma distribution_integral_pairing_linear c f g x:
  ed (xi x) (value (c*:f+g) x)=c*ed (xi x) (value f x)+ed (xi x) (value g x).
Proof.
have hValues:=congr1 (fun F:X->Y=>F x) (hom_linear (smooth_test_values_hom hE) c f g).
change (value (c*:f+g) x=c*:value f x+value g x) in hValues.
rewrite hValues; exact:(hom_linear (ed (xi x)) c (value f x) (value g x)).
Qed.

(** Source for [distribution_integral_functional_exists]:
    a real linear functional has exactly the
    printed pairing integrals on all tests,
    supporting Federer 4.1.1, p. 346. *)
Theorem distribution_integral_functional_exists:
  exists T:Hom DT R^o,is_distribution_integral_action mu ed xi value T.
Proof.
exact:(@real_integral_linear_map_exists R X DT mu hm
  (fun f x=>ed (xi x) (value f x)) distribution_integral_pairing_linear
  distribution_integral_pairing_finite).
Qed.
End IntegralFunctionalExistence.
