(** Federer (1969), 4.1.1, p. 346: if the
    weak density xi is C1 in dual norm,
    the distribution D_v T=-TD_v corresponds
    to the actual field D_v xi. The compact
    vector test supplies all support bounds. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws NormClassOneUP
  NormRegularity LinearBasis ContinuousMultilinearSealed ContinuousDualUP ContinuousDualNorm
  TopologicalBorel MeasureUP MeasurePushforward MeasureIntegralUP MeasureIntegralUniqueness
  SummableRealFunctionUP SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionDerivativesUP
  SmoothFunctionSupport SmoothGlobalFirstDifferential SmoothTestSpaces SmoothTestEvaluation SmoothTestTopology
  SmoothDirectionalDerivativeSealed TestDirectionalOperator ContinuousRealDual DistributionDirectionalDerivative
  DistributionIntegralFieldUP CompactDualPairingIntegrationByParts.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section DistributionIntegralByParts.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable YD:lmodType R.
Variable ed:Hom YD (Hom Y R^o).
Variable DN:YD->R.
Hypothesis hYD:is_continuous_dual hNY ed DN.
Variable d:nat.
Variable b:'I_d->X.
Hypothesis hb:is_basis b.
Variable mu:set X->\bar R.
Hypothesis hm:is_measure mu.
Hypothesis hB:forall A:set X,@borel_set (real_norm_metric_space hNX) A ->measure_measurable mu A.
Hypothesis hK:forall C:set X,@compact (real_norm_metric_space hNX) C ->(mu C< +oo)%E.
Hypothesis hInvariant:forall c:X,measure_pushforward (fun x=>x+c) mu=mu.
Variable xi:X->YD.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY (fun _=>True) ev.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY (fun _=>True) E ev D.
Local Notation DT := (smooth_test_space hE).
Local Notation inc := (smooth_test_inclusion hE).
Local Notation value := (smooth_test_value hE).
Local Notation SO := (smooth_test_opens hE hD).
Local Notation hSO := (smooth_test_final_topology_laws hE hD).1.
Local Notation DD := (@continuous_real_dual_space R DT SO hSO).
Local Notation eD := (@continuous_real_dual_evaluation R DT SO hSO).
Local Notation hFull := (fun x (_:True)=>norm_full_domain_interior NX x).
Variable v:X.
Local Notation P := (@SmoothDirectionalDerivative.operator R X Y NX NY hNX hNY (fun _=>True) E ev hE D hD v).
Local Notation hP := (@SmoothDirectionalDerivative.laws R X Y NX NY hNX hNY (fun _=>True) E ev hE D hD v).
Local Notation Q := (@distribution_test_directional_derivative R X Y NX NY hNX hNY (fun _=>True) hFull E ev hE D hD v).
Local Notation deriv := (@distribution_directional_derivative R X Y NX NY hNX hNY (fun _=>True) hFull E ev hE D hD v).

(** Source for [distribution_integral_derivative_action]:
    D_v T is precisely the distribution of
    D_v xi, the integration-by-parts conclusion
    in Federer 4.1.1, p. 346. The
    candidate derivative field is the actual
    C1 differential evaluated at v. *)
Theorem distribution_integral_derivative_action (T:DD) (DXi:X->Hom X YD):
  is_distribution_integral_action mu ed xi value (eD T) ->
  is_norm_class_one_field NX DN (fun _=>True) xi DXi ->
  is_distribution_integral_action mu ed (fun x=>DXi x v) value (eD (deriv T)).
Proof.
move=>hAction hXi f.
pose DPhi:=@smooth_global_first_differential R X Y NX NY hNX hNY E D (inc f).
have hPhi:=@smooth_global_first_differential_class_one R X Y NX NY hNX hNY E ev hE D hD (inc f).
have [K hSupport]:=smooth_test_support_bound hE f.
have hZero x:~smooth_compact_carrier K x ->value f x=0.
  exact:((smooth_function_compact_support_iff hE K (inc f)).1 hSupport x).
have [a [hA hIntegral]]:=@compact_dual_pairing_integration_by_parts R X Y YD NX NY hNX hNY ed DN hYD
  d b hb mu hm hB hK hInvariant K (value f) xi DPhi DXi v hPhi hXi hZero.
have hTestValue x:value (Q f) x=DPhi x v.
  change (ev (inc (Q f)) x=DPhi x v).
  rewrite (@test_directional_evaluation R X Y NX NY hNX hNY (fun _=>True) hFull E ev hE D hD v P hP).
  exact:(@SmoothDirectionalDerivative.laws R X Y NX NY hNX hNY (fun _=>True) E ev hE D hD v
    (inc f) x Logic.I).
have hActionQ:=hAction (Q f).
have hEq:(fun x=>ed (xi x) (value (Q f) x))=(fun x=>ed (xi x) (DPhi x v)).
  apply:funext=>x; by rewrite hTestValue.
rewrite hEq in hActionQ.
have hEqual:eD T (Q f)=a:=congr1 (@fine R) (measure_integral_unique hActionQ hA).
have hEval:=@distribution_directional_derivative_evaluation R X Y NX NY hNX hNY
  (fun _=>True) hFull E ev hE D hD v T f.
by rewrite hEval hEqual.
Qed.
End DistributionIntegralByParts.
