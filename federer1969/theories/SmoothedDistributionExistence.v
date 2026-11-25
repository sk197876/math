(** Federer (1969), 4.1.2, pp. 347-348:
    the original smoothed test action is an actual
    distribution, represented by its actual smooth Y*-valued
    kernel density. Continuity follows from the proved
    integral action and the original 4.1.1 field theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws NormRegularity CompleteMetricUP
  VectorDaniellHypotheses ContinuousDualUP ContinuousDualNorm ContinuousMultilinearSealed
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  OpenFamilyTopologyUP NormOpenTopology WeakEvaluationTopologySealed
  SmoothFunctionSpaceUP SmoothFunctionSpaceSealed SmoothFunctionDerivativesUP SmoothFunctionDerivativesSealed
  SmoothGlobalTranslationSealed SmoothTestSpaces SmoothTestEvaluation SmoothTestTopology ContinuousRealDual
  EuclideanLebesgueDimensions EuclideanDistributionMeasureContext
  DistributionIntegralFieldUP DistributionIntegralFunctionalContinuity
  TranslatedKernelTestUP SmoothedDistributionDensityUP SmoothedDistributionDensityExistence SmoothedDistributionDensitySmoothness
  ContinuousDualFieldLocalIntegrability SmoothSmoothingFamilyUP SmoothingDistributionIntegralAction SmoothedDistributionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SmoothedDistributionExistence.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NS := (fun t:R^o=>`|t|).
Local Notation hNS := (@scalar_absolute_value_norm R).
Local Notation mu := (@euclidean_lebesgue_measure R n).
Local Notation hm := (euclidean_lebesgue_is_measure R n).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Hypothesis hY:is_complete_metric_space (real_norm_metric_space hNY).
Hypothesis hSep:is_separable_normed_space hNY.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hN hNY (fun _=>True) ev.
Variable D:forall j,X->Hom E (@ContinuousMultilinear.space R j X Y N NY hN hNY).
Hypothesis hD:@is_smooth_function_derivatives R X Y N NY hN hNY (fun _=>True) E ev D.
Local Notation DT := (smooth_test_space hE).
Local Notation SO := (smooth_test_opens hE hD).
Local Notation hSO := (smooth_test_final_topology_laws hE hD).1.
Local Notation DD := (@continuous_real_dual_space R DT SO hSO).
Local Notation eD := (@continuous_real_dual_evaluation R DT SO hSO).
Variable psi:X->R.
Hypothesis hPsi:norm_class_all_orders hN hNS (fun _=>True) psi.
Variable r:R.
Hypothesis hOff:forall x,r<N x ->psi x=0.
Hypothesis hRadius:0<=r.
Variable B:X->Hom Y DT.
Hypothesis hB:@is_translated_kernel_tests R X Y N NY hN hNY E ev hE psi B.
Variable P:Hom E E.
Hypothesis hP:is_smooth_smoothing_operator hNY ev psi P.
Variable Q:Hom DT DT.
Hypothesis hQ:forall f,smooth_test_inclusion hE (Q f) = P (smooth_test_inclusion hE f).
Variable T:Hom DT R^o.
Hypothesis hT:open_family_continuous SO (norm_open_family hNS) T.
Variable YD:lmodType R.
Variable ed:Hom YD (Hom Y R^o).
Variable DN:YD->R.
Hypothesis hYD:is_continuous_dual hNY ed DN.
Local Notation hDN := (continuous_dual_norm_is_norm hYD).

(** Source for [smoothed_distribution_exists_with_density]: the complete
    original existence and smooth-density representation of T_epsilon
    in Federer 4.1.2, pp. 347-348. The
    actual continuous dual is used, and the test action
    is exactly T(Phi*f), with no continuity premise on it. *)
Theorem smoothed_distribution_exists_with_density:
  exists A:DD,is_smoothed_distribution eD T Q A /\
    exists xi:X->YD,norm_class_all_orders hN hDN (fun _=>True) xi /\
      is_smoothed_distribution_density B T ed xi /\
      is_distribution_integral_action mu ed xi (smooth_test_value hE) (eD A).
Proof.
have[xi hXi]:=@smoothed_distribution_density_exists R n Y NY hNY E ev hE D hD
  psi hPsi r hOff B hB T hT YD ed DN hYD.
have hSmooth:=@smoothed_distribution_density_smooth R n Y NY hNY E ev hE D hD
  T hT YD ed DN hYD psi r B xi hPsi hOff hB hXi.
pose hFull:=fun x (_:True)=>norm_full_domain_interior N x.
pose S:=@SmoothFunctionSpace.space R X R^o N NS hN hNS (fun _=>True) hFull.
pose sv:=@SmoothFunctionSpace.value R X R^o N NS hN hNS (fun _=>True) hFull.
pose hS:=@SmoothFunctionSpace.laws R X R^o N NS hN hNS (fun _=>True) hFull.
pose DS:=@SmoothFunctionDerivatives.operators R X R^o N NS hN hNS (fun _=>True) S sv hS.
pose hDS:=@SmoothFunctionDerivatives.laws R X R^o N NS hN hNS (fun _=>True) S sv hS.
pose L:=@SmoothGlobalTranslation.operator R X R^o N NS hN hNS S sv hS.
have hL c:=@SmoothGlobalTranslation.laws R X R^o N NS hN hNS S sv hS c.
have[s hs]:=smooth_function_evaluation_surjective hS hPsi.
have hValue x:sv s x=psi x:=hs x Logic.I.
pose U:=hom_comp T Q.
have hAction:is_distribution_integral_action mu ed xi (smooth_test_value hE) U.
  exact:(@smoothing_distribution_integral_action R n Y NY hNY hY hSep
    S sv hS DS hDS s psi hValue r hOff E ev hE D hD L hL B hB T hT
    YD ed DN hYD xi hXi hRadius P hP Q hQ).
pose O:=@WeakEvaluationTopology.opens R Y YD (fun a y=>ed a y).
pose hO:=@WeakEvaluationTopology.laws R Y YD (fun a y=>ed a y).
have hField:=@continuous_dual_field_locally_integrable R n Y NY hNY YD ed DN hYD O hO
  xi (norm_class_continuous (hSmooth 0%N)).
have hContinuous:open_family_continuous SO (norm_open_family hNS) U.
  exact:(@distribution_integral_action_continuous R X Y N NY hN hNY YD ed DN hYD hSep O hO
    mu hm (@euclidean_distribution_measure_open R n) xi
    (@integrable_dual_field_weak_measurable R X Y N hN YD ed DN O hO mu xi hField)
    E ev hE D hD
    (@integrable_dual_field_local_norm R X Y N hN YD ed DN O hO mu xi hField)
    U hAction).
have[A hA]:=@continuous_real_dual_represents R DT SO hSO U hContinuous.
exists A; split.
- move=>f; by rewrite hA /U hom_compE.
- exists xi; split; first exact hSmooth.
  split; first exact hXi.
  by rewrite hA.
Qed.
End SmoothedDistributionExistence.
