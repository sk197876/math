(** Federer (1969), 4.1.1, pp. 345–346: ordinary
    scalar integration is an actual distribution. The
    constant scalar dual field has unit norm and
    therefore satisfies the original local integrability
    condition for every measure finite on compact sets. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric ContinuousMultilinearSealed ContinuousDualUP ContinuousDualSealed
  VectorDaniellHypotheses LocalUniquenessExample OpenFamilyTopologyMathcomp WeakEvaluationTopologyUP WeakEvaluationTopologySealed
  PartialFunctionBasic MeasureUP MeasurableFunctionUP MeasureIntegralUP SummableRealFunctionUP CharacteristicFunctionUP CharacteristicFunctionSealed
  MeasureCharacteristicIntegral MeasurableTotalBasic SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionDerivativesUP
  SmoothTestSpaces SmoothTestEvaluation SmoothTestTopology SmoothCompactTestMeasurable ContinuousRealDual
  ScalarIdentityDualFunctional DistributionIntegralFieldUP DistributionIntegralFunctionalContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ScalarIntegralDistribution.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Hypothesis hNX:is_real_norm NX.
Variable mu:set X->\bar R.
Hypothesis hm:is_measure mu.
Hypothesis hOpen:forall A:set X,@open (real_norm_metric_space hNX) A ->measure_measurable mu A.
Hypothesis hCompact:forall C:set X,@compact (real_norm_metric_space hNX) C ->(mu C< +oo)%E.
Variable E:lmodType R.
Variable ev:E->X->R^o.
Hypothesis hE:is_smooth_function_space hNX (@scalar_absolute_value_norm R) (fun _=>True) ev.
Variable D:forall k,X->Hom E (@ContinuousMultilinear.space R k X R^o NX (fun t:R^o=>`|t|) hNX (@scalar_absolute_value_norm R)).
Hypothesis hD:@is_smooth_function_derivatives R X R^o NX (fun t:R^o=>`|t|) hNX (@scalar_absolute_value_norm R)
  (fun _=>True) E ev D.
Local Notation DT := (smooth_test_space hE).
Local Notation SO := (smooth_test_opens hE hD).
Local Notation hSO := (smooth_test_final_topology_laws hE hD).1.
Local Notation DD := (@continuous_real_dual_space R DT SO hSO).
Local Notation eD := (@continuous_real_dual_evaluation R DT SO hSO).

(** Source for [scalar_integral_distribution_exists]: the
    original integral formula produces a distribution for
    the constant scalar identity field, Federer 4.1.1,
    p. 346. Its support is not assumed compact. *)
Theorem scalar_integral_distribution_exists:
  exists T:DD,forall f:DT,is_measure_integral mu
    (real_total_integrand (smooth_test_value hE f)) (eD T f)%:E.
Proof.
pose hR:=@scalar_absolute_value_norm R.
pose YD:=@ContinuousDual.space R R^o (fun t:R^o=>`|t|) hR.
pose ed:=@ContinuousDual.evaluation R R^o (fun t:R^o=>`|t|) hR.
pose DN:=@ContinuousDual.norm R R^o (fun t:R^o=>`|t|) hR.
pose hYD:=@ContinuousDual.laws R R^o (fun t:R^o=>`|t|) hR.
have [a [hEval hNorm]]:=scalar_identity_dual_functional_exists hYD.
pose O:=@WeakEvaluationTopology.opens R R^o YD (fun a y=>ed a y).
pose hO:=@WeakEvaluationTopology.laws R R^o YD (fun a y=>ed a y).
have hXi:is_measure_measurable_function mu
  (partial_function_total (fun _:X=>(a:open_family_topological_space hO.1))).
  exact:(@measurable_total_constant R X (open_family_topological_space hO.1) mu hm a).
have hLocal (K:smooth_compact_set hNX (fun _=>True)):exists b:R,is_measure_integral mu
    (real_total_integrand (fun x=>if pselect (smooth_compact_carrier K x) then DN a else 0)) b%:E.
  have hKM:=@smooth_compact_set_measurable R X NX hNX mu hOpen K.
  have hK0:=measure_nonnegative hm (smooth_compact_carrier K).
  have hKFin:=@hCompact _ (smooth_compact_is_compact K).
  have hFinite:mu (smooth_compact_carrier K) \is a fin_num by rewrite (ge0_fin_numE hK0).
  pose b:=fine (mu (smooth_compact_carrier K)).
  have hMass:mu (smooth_compact_carrier K)=b%:E by rewrite /b fineK.
  pose chi:=@CharacteristicFunction.value R X (smooth_compact_carrier K).
  have hChi:=@CharacteristicFunction.laws R X (smooth_compact_carrier K).
  have hInt:=@measure_characteristic_integral R X mu hm (smooth_compact_carrier K) chi hChi hKM.
  have hEq:(fun x=>if pselect (smooth_compact_carrier K x) then DN a else 0)=chi.
    apply:funext=>x; case:(pselect (smooth_compact_carrier K x))=>hx.
    - rewrite /chi (characteristic_on_set hChi hx); exact hNorm.
    - by rewrite /chi (characteristic_off_set hChi hx).
  exists b; rewrite hEq; by rewrite -hMass.
have [T hAction]:=@distribution_from_dual_field_exists R X R^o NX (fun t:R^o=>`|t|) hNX hR
  YD ed DN hYD (@scalar_norm_separable R) O hO mu hm hOpen (fun _=>a) hXi E ev hE D hD hLocal.
exists T=>f.
have h:=hAction f.
have hEq:(fun x=>ed a (smooth_test_value hE f x))=smooth_test_value hE f.
  apply:funext=>x; exact:hEval.
by rewrite hEq in h.
Qed.
End ScalarIntegralDistribution.
