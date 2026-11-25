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
  ContinuousDualFieldLocalIntegrability SmoothSmoothingFamilyUP SmoothingDistributionIntegralAction SmoothedDistributionUP SmoothedDistributionExistence LinearSubspaceRepresentationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SmoothedDistributionDensityCharacterization.
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


Variable A:DD.
Hypothesis hA:is_smoothed_distribution eD T Q A.

(** Source for [smoothed_distribution_has_smooth_density]: every
    actual distribution with the original smoothed test action
    has the stated norm-smooth Y*-valued density and the actual
    integral representation, Federer 4.1.2, pp. 347-348.
    No separability of the full dual is imposed. *)
Theorem smoothed_distribution_has_smooth_density:
  exists xi:X->YD,norm_class_all_orders hN hDN (fun _=>True) xi /\
    is_smoothed_distribution_density B T ed xi /\
    is_distribution_integral_action mu ed xi (smooth_test_value hE) (eD A).
Proof.
have[C [hC [xi [hSmooth [hXi hAction]]]]]:=@smoothed_distribution_exists_with_density
  R n Y NY hNY hY hSep E ev hE D hD psi hPsi r hOff hRadius B hB P hP Q hQ T hT YD ed DN hYD.
have hEqual:A=C.
  apply:(@smoothed_distribution_unique R DT DD eD T Q A C _ hA hC).
  exact:(subspace_representation_injective (@continuous_real_dual_model_laws R DT SO hSO)).
exists xi; split; first exact hSmooth.
split; first exact hXi.
by rewrite hEqual.
Qed.
End SmoothedDistributionDensityCharacterization.
