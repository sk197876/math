(** Federer (1969), 4.1.7, pp. 355–358:
    locally integrable weak dual fields on the original
    open U define actual distributions on U. The
    construction uses the existing compact pairing
    integral and the original fixed-support continuity
    criterion of 4.1.1, pp. 345–346. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import NormDifferentialUP Hom RealNormUP NormMetric RealMetricBackground ContinuousDualUP
  ContinuousMultilinearSealed VectorDaniellHypotheses OpenFamilyTopologyMathcomp WeakEvaluationTopologyUP
  WeakEvaluationMeasurableCoordinates PartialFunctionBasic MeasureUP RadonMeasureUP RadonBorelRegularity
  MeasurableFunctionUP MeasureIntegralUP SummableRealFunctionUP IsotropyGroupTopology
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothFunctionSupport
  SmoothTestSpaces SmoothTestEvaluation SmoothFunctionSeminormFamily SmoothFunctionTopology
  SmoothDerivativeSeminormUP DistributionVariationDomain DistributionSubspaceTestValues
  CompactContinuousVectorMeasurable IntegrableCompactDualPairing
  OpenDistributionIntegralTestBound DistributionIntegralFieldUP RealIntegralLinearMapExistence
  SmoothFunctionSpaceLaws SmoothTestTopology DistributionLocalBound OpenFamilyTopologyUP NormOpenTopology
  MeasureIntegralUniqueness LinearSubspaceRepresentationUP ContinuousRealDual.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section OpenDistributionFromField.
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

Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Hypothesis hLocal:forall K:smooth_compact_set hNX U,exists b:R,
  is_measure_integral mu (real_total_integrand
    (fun x:UT=>if pselect (smooth_compact_carrier K (set_val x)) then DN (xi x) else 0)) b%:E.
Local Notation SO := (smooth_test_opens hE hD).
Local Notation hSO := (smooth_test_final_topology_laws hE hD).1.
Local Notation DD := (@continuous_real_dual_space R DT SO hSO).
Local Notation evaluation := (@continuous_real_dual_evaluation R DT SO hSO).

(** Source for [open_distribution_pairing_finite]: every
    original compact test has a finite pairing integral
    over U, supporting Federer 4.1.7, pp. 356–358. *)
Lemma open_distribution_pairing_finite f:
  exists c:R,is_measure_integral mu (real_total_integrand
    (fun x=>ed (xi x) (dvalues f x))) c%:E.
Proof.
have [K hK]:=smooth_test_support_bound hE f.
have [b hb]:=hLocal K.
have [c [hc hBound]]:=@open_distribution_integral_test_bound R X Y NX NY hNX hNY U E ev hE D hD
  YD ed DN hYD hSep O hO mu hm hr xi hXi K b f hK hb.
by exists c.
Qed.

(** Source for [open_distribution_pairing_linear]: the
    original pairing integrand is linear in the actual
    test on U, supporting Federer 4.1.7, pp. 356–358. *)
Lemma open_distribution_pairing_linear c f g x:
  ed (xi x) (dvalues (c*:f+g) x)=
    c*ed (xi x) (dvalues f x)+ed (xi x) (dvalues g x).
Proof.
have hValues:=congr1 (fun F:UT->Y=>F x) (hom_linear dvalues c f g).
change (dvalues (c*:f+g) x=c*:dvalues f x+dvalues g x) in hValues.
rewrite hValues;exact:(hom_linear (ed (xi x)) c (dvalues f x) (dvalues g x)).
Qed.

(** Source for [open_distribution_integral_functional_exists]:
    the original integral action on U is an actual
    linear functional on compact tests, supporting
    Federer 4.1.7, pp. 356–358. *)
Theorem open_distribution_integral_functional_exists:
  exists L:Hom DT R^o,is_distribution_integral_action mu ed xi dvalues L.
Proof.
exact:(@real_integral_linear_map_exists R UT DT mu hm
  (fun f x=>ed (xi x) (dvalues f x)) open_distribution_pairing_linear open_distribution_pairing_finite).
Qed.

(** Source for [open_distribution_integral_action_continuous]:
    the actual integral functional is continuous for
    the original literal final topology on D(U,Y),
    supporting Federer 4.1.7, pp. 356–358. *)
Theorem open_distribution_integral_action_continuous (L:Hom DT R^o):
  is_distribution_integral_action mu ed xi dvalues L->
  open_family_continuous SO (norm_open_family (@scalar_absolute_value_norm R)) L.
Proof.
move=>hAction.
apply:(@distribution_continuity_local_bound R X Y NX NY hNX hNY U hU E ev hE D hD L).2=>K.
have [b hIntegral]:=hLocal K.
pose M:=Num.bound (Num.max b 0).
have hMax:0<=Num.max b 0 by rewrite le_max lexx orbT.
have hNat:b<=M%:R.
  have hBound:Num.max b 0<M%:R:=archi_boundP hMax.
  have hbMax:b<=Num.max b 0 by rewrite le_max lexx.
  exact:(le_trans hbMax (ltW hBound)).
exists 0%N,M=>f.
pose g:=smooth_test_step hE K f.
have hSupport:@smooth_function_support R X Y NX hNX U E ev (inc g) `<=` smooth_compact_carrier K.
  rewrite /g smooth_test_step_evaluation.
  exact:(subspace_representation_member (smooth_fixed_test_space_laws hE K) f).
have [c [hc hBound]]:=@open_distribution_integral_test_bound R X Y NX NY hNX hNY U E ev hE D hD
  YD ed DN hYD hSep O hO mu hm hr xi hXi K b g hSupport hIntegral.
have hEqual:L g=c:=congr1 (@fine R) (measure_integral_unique (hAction g) hc).
rewrite -hEqual /g smooth_test_step_evaluation in hBound.
have hNu:=smooth_derivative_seminorm_nonnegative (smooth_function_derivative_seminorm_laws hD K 0%N)
  (smooth_fixed_test_inclusion hE K f).
have hProduct:=ler_wpM2r hNu hNat.
rewrite (mulrC (nu K 0%N (smooth_fixed_test_inclusion hE K f)) b) in hBound.
exact:(le_trans hBound hProduct).
Qed.

(** Source for [open_distribution_from_dual_field_exists]:
    the original Radon pairing on U defines an
    actual continuous distribution, supporting Federer
    4.1.7, pp. 355–358. No extension outside U
    or unproved continuity premise is used. *)
Theorem open_distribution_from_dual_field_exists:
  exists T:DD,is_distribution_integral_action mu ed xi dvalues (evaluation T).
Proof.
have [L hAction]:=open_distribution_integral_functional_exists.
have hContinuous:=open_distribution_integral_action_continuous hAction.
have [T hEval]:=@continuous_real_dual_represents R DT SO hSO L hContinuous.
exists T;by rewrite hEval.
Qed.
End OpenDistributionFromField.
