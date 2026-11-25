(** Federer (1969), 4.1.2, pp. 347-348:
    the original smoothed test action is an actual
    distribution, represented by its actual smooth Y*-valued
    kernel density. Continuity follows from the proved
    integral action and the original 4.1.1 field theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws NormRegularity CompleteMetricUP
  VectorDaniellHypotheses ContinuousDualUP ContinuousDualNorm ContinuousDualSealed ContinuousMultilinearSealed
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  OpenFamilyTopologyUP NormOpenTopology WeakEvaluationTopologySealed
  SmoothFunctionSpaceUP SmoothFunctionSpaceSealed SmoothFunctionDerivativesUP SmoothFunctionDerivativesSealed
  SmoothGlobalTranslationSealed SmoothTestSpaces SmoothTestEvaluation SmoothTestTopology ContinuousRealDual
  EuclideanLebesgueDimensions EuclideanDistributionMeasureContext
  DistributionIntegralFieldUP DistributionIntegralFunctionalContinuity
  TranslatedKernelTestUP SmoothedDistributionDensityUP SmoothedDistributionDensityExistence SmoothedDistributionDensitySmoothness
  ContinuousDualFieldLocalIntegrability SmoothSmoothingFamilyUP SmoothingDistributionIntegralAction SmoothedDistributionUP
  SmoothingKernelUP SmoothingDilationUP SmoothingDilationSmooth SmoothingDilationNonzeroRadius
  TestSmoothingFamilyUP TranslatedKernelTestSealed SmoothedDistributionExistence
  SmoothedDistributionFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SmoothedDistributionFamilyExistence.
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

Variable phi:X->R.
Hypothesis hPhi:is_smoothing_kernel phi.
Variable family:R->X->R.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable P:R->Hom E E.
Hypothesis hP:is_smooth_smoothing_family hNY ev family P.
Variable Q:R->Hom DT DT.
Hypothesis hQ:@is_test_smoothing_family R X Y N NY hN hNY (fun _=>True) E ev hE P Q.
Variable T:Hom DT R^o.
Hypothesis hT:open_family_continuous SO (norm_open_family hNS) T.

(** Source for [smoothed_distribution_family_exists]: the actual
    positive-parameter family of distributions in Federer 4.1.2,
    p. 347. Each continuous-dual member is obtained by the proved
    kernel integral representation, rather than an assumed operator. *)
Theorem smoothed_distribution_family_exists:
  exists A:R->DD,is_smoothed_distribution_family eD T Q A.
Proof.
have hFor e:exists a:DD,0<e ->is_smoothed_distribution eD T (Q e) a.
  case:(pselect (0<e))=>he; last first.
    exists 0; by move=>h; exfalso; exact:he h.
  have hPsi:=@smoothing_dilation_smooth R n phi hPhi family hFamily e he.
  have hOff:=@smoothing_dilation_zero_beyond_radius R n phi family hPhi hFamily e he.
  pose B:=@TranslatedKernelTest.value R n Y NY hNY E ev hE (family e) hPsi e hOff.
  have hB:=@TranslatedKernelTest.laws R n Y NY hNY E ev hE (family e) hPsi e hOff.
  pose YD:=@ContinuousDual.space R Y NY hNY.
  pose ed:=@ContinuousDual.evaluation R Y NY hNY.
  pose DN:=@ContinuousDual.norm R Y NY hNY.
  pose hYD:=@ContinuousDual.laws R Y NY hNY.
  have[a [hA _]]:=@smoothed_distribution_exists_with_density R n Y NY hNY hY hSep
    E ev hE D hD (family e) hPsi e hOff (ltW he) B hB
    (P e) (@hP e he) (Q e) (@hQ e he) T hT YD ed DN hYD.
  exists a; by move=>_.
have[A hA]:=choice hFor.
exists A=>e he; exact:hA e he.
Qed.
End SmoothedDistributionFamilyExistence.
