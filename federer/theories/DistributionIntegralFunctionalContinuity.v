(** Federer (1969), 4.1.1, p. 346: the
    actual integral functional is continuous on
    D and hence is an actual distribution.
    The original local order-zero bound proves
    continuity on every same-compact test step. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric RealMetricBackground NormOpenDomainLaws NormRegularity
  ContinuousMultilinearSealed ContinuousDualUP VectorDaniellHypotheses
  OpenFamilyTopologyMathcomp WeakEvaluationTopologyUP WeakEvaluationMeasurableCoordinates
  PartialFunctionBasic MeasureUP MeasurableFunctionUP MeasureIntegralUP MeasureIntegralUniqueness SummableRealFunctionUP
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothFunctionSupport
  SmoothDerivativeSeminormUP SmoothFunctionTopology SmoothTestSpaces SmoothTestEvaluation
  SmoothCompactTestMeasurable IntegrableCompactDualPairing DistributionIntegralFieldUP
  DistributionIntegralTestBound DistributionIntegralFunctionalExistence SmoothFunctionSpaceLaws
  ModuleQuotient LinearSubspaceRepresentationUP OpenFamilyTopologyUP NormOpenTopology
  SmoothTestTopology DistributionLocalBound ContinuousRealDual.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section IntegralFunctionalContinuity.
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

Local Notation SO := (smooth_test_opens hE hD).
Local Notation hSO := (smooth_test_final_topology_laws hE hD).1.
Local Notation DD := (@continuous_real_dual_space R DT SO hSO).
Local Notation eD := (@continuous_real_dual_evaluation R DT SO hSO).

(** Source for [distribution_integral_action_continuous]:
    the original pairing integral defines a
    continuous real functional on D, Federer
    4.1.1, p. 346. Each original compact
    K has derivative order zero and a finite
    integer constant. *)
Theorem distribution_integral_action_continuous (T:Hom DT R^o):
  is_distribution_integral_action mu ed xi value T ->
  open_family_continuous SO (norm_open_family (@scalar_absolute_value_norm R)) T.
Proof.
move=>hAction.
apply:(@distribution_continuity_local_bound R X Y NX NY hNX hNY (fun _=>True)
  (fun x _=>norm_full_domain_interior NX x) E ev hE D hD T).2=>K.
have [b hIntegral]:=hLocal K.
pose M:=Num.bound (Num.max b 0).
have hMax:0<=Num.max b 0 by rewrite le_max lexx orbT.
have hNat: b<=M%:R.
  have hBound:Num.max b 0<M%:R:=archi_boundP hMax.
  have hbMax:b<=Num.max b 0 by rewrite le_max lexx.
  exact:(le_trans hbMax (ltW hBound)).
exists 0%N,M=>f.
pose g:=smooth_test_step hE K f.
have hSupport:support (inc g) `<=` smooth_compact_carrier K.
  rewrite /g smooth_test_step_evaluation.
  exact:(subspace_representation_member (smooth_fixed_test_space_laws hE K) f).
have [c [hc hBound]]:=@distribution_integral_test_bound R X Y NX NY hNX hNY YD ed DN hYD hSep O hO
  mu hm hOpen xi hXi E ev hE D hD K b g hSupport hIntegral.
have hEqual:T g=c:=congr1 (@fine R) (measure_integral_unique (hAction g) hc).
rewrite -hEqual /g smooth_test_step_evaluation in hBound.
have hNu:=smooth_derivative_seminorm_nonnegative (smooth_function_derivative_seminorm_laws hD K 0%N)
  (smooth_fixed_test_inclusion hE K f).
have hProduct:=ler_wpM2r hNu hNat.
rewrite (mulrC (nu K 0%N (smooth_fixed_test_inclusion hE K f)) b) in hBound.
exact:(le_trans hBound hProduct).
Qed.

(** Source for [distribution_from_dual_field_exists]: the
    original weak field with locally integrable
    norm produces an actual distribution with
    exactly the printed integral values,
    Federer 4.1.1, p. 346. *)
Theorem distribution_from_dual_field_exists:
  exists T:DD,is_distribution_integral_action mu ed xi value (eD T).
Proof.
have [L hAction]:=@distribution_integral_functional_exists R X Y NX NY hNX hNY YD ed DN hYD hSep O hO
  mu hm hOpen xi hXi E ev hE D hD hLocal.
have hContinuous:=distribution_integral_action_continuous hAction.
have [T hEval]:=@continuous_real_dual_represents R DT SO hSO L hContinuous.
exists T; by rewrite hEval.
Qed.
End IntegralFunctionalContinuity.
