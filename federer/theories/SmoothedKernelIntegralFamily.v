(** Federer (1969), 4.1.4, p. 349, using 4.1.2:
    the actual positive-scale density family gives the
    original distribution integral for every actual test.
    This instantiates the released arbitrary-Banach integral
    interchange without a new range assumption. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom ModuleQuotient NormOpenTopology OpenFamilyTopologyUP MetricClosedBalls RealNormUP NormMetric CompleteMetricUP VectorDaniellHypotheses
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness ContinuousMultilinearSealed
  LinearSubspaceRepresentationUP SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSupport SmoothFunctionDerivativesUP
  SmoothFunctionTopology SmoothTestEvaluation SmoothTestSpaces SmoothTestTopology SmoothingKernelUP SmoothingDilationUP
  SmoothSmoothingFamilyUP SmoothSmoothingSupport SmoothSmoothingConvergence
  SmoothSupportedPositiveLimit TestSmoothingFamilyUP ContinuousTestSmoothingConvergence
  SmoothFunctionSpaceSealed SmoothFunctionDerivativesSealed SmoothGlobalTranslationSealed NormOpenDomainLaws
  EuclideanLebesgueDimensions ContinuousDualUP SmoothingDilationSmooth SmoothingDilationNonzeroRadius SmoothedKernelDensityFamily
  ContinuousDistributionIntegralAction DistributionIntegralFieldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SmoothedKernelIntegralFamily.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Hypothesis hY:is_complete_metric_space (real_norm_metric_space hNY).
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hN hNY (fun _=>True) ev.
Local Notation Z := (fun j=>@ContinuousMultilinear.space R j X Y N NY hN hNY).
Variable D:forall j,X->Hom E (Z j).
Hypothesis hD:@is_smooth_function_derivatives R X Y N NY hN hNY (fun _=>True) E ev D.
Local Notation DT := (smooth_test_space hE).
Local Notation inc := (smooth_test_inclusion hE).
Local Notation support := (@smooth_function_support R X Y N hN (fun _=>True) E ev).
Local Notation SO := (smooth_test_opens hE hD).
Local Notation nu := (smooth_function_derivative_seminorm hD).
Variable phi:X->R.
Hypothesis hPhi:is_smoothing_kernel phi.
Variable family:R->X->R.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable P:R->Hom E E.
Hypothesis hP:is_smooth_smoothing_family hNY ev family P.
Variable Q:R->Hom DT DT.
Hypothesis hQ:@is_test_smoothing_family R X Y N NY hN hNY (fun _=>True) E ev hE P Q.


Variable T:Hom DT R^o.
Hypothesis hT:open_family_continuous SO (norm_open_family (@scalar_absolute_value_norm R)) T.


Variable YD:lmodType R.
Variable ed:Hom YD (Hom Y R^o).
Variable DN:YD->R.
Hypothesis hYD:is_continuous_dual hNY ed DN.
Variable B:R->X->Hom Y DT.
Variable g:R->X->YD.
Hypothesis hBG:@is_smoothed_kernel_density_family R n Y NY hNY E ev hE T YD ed family B g.

(** Source for [smoothed_kernel_density_integral_action]: the
    original integral action of every g_e used in both
    limits of Federer 4.1.4, p. 349. No separability of Y
    or Y* is added; the actual original test integral is used. *)
Theorem smoothed_kernel_density_integral_action e:0<e ->
  is_distribution_integral_action (@euclidean_lebesgue_measure R n) ed (g e)
    (smooth_test_value hE) (hom_comp T (Q e)).
Proof.
move=>he.
pose hNS:=@scalar_absolute_value_norm R.
pose NS:=fun t:R^o=>`|t|.
pose hFull:=fun x (_:True)=>norm_full_domain_interior N x.
pose S:=@SmoothFunctionSpace.space R X R^o N NS hN hNS (fun _=>True) hFull.
pose sv:=@SmoothFunctionSpace.value R X R^o N NS hN hNS (fun _=>True) hFull.
pose hS:=@SmoothFunctionSpace.laws R X R^o N NS hN hNS (fun _=>True) hFull.
pose DS:=@SmoothFunctionDerivatives.operators R X R^o N NS hN hNS (fun _=>True) S sv hS.
pose hDS:=@SmoothFunctionDerivatives.laws R X R^o N NS hN hNS (fun _=>True) S sv hS.
pose L:=@SmoothGlobalTranslation.operator R X R^o N NS hN hNS S sv hS.
have hL c:=@SmoothGlobalTranslation.laws R X R^o N NS hN hNS S sv hS c.
pose hSmooth:=@smoothing_dilation_smooth R n phi hPhi family hFamily e he.
pose hOff:=@smoothing_dilation_zero_beyond_radius R n phi family hPhi hFamily e he.
have[s hs]:=smooth_function_evaluation_surjective hS hSmooth.
have hF x:sv s x=family e x:=hs x Logic.I.
have[hB hg]:=@hBG e he.
exact:(@continuous_distribution_integral_action R n Y NY hNY hY
  S sv hS DS hDS s (family e) hF e hOff E ev hE D hD
  L hL (B e) hB T hT YD ed DN hYD (g e) hg (ltW he)
  (P e) (@hP e he) (Q e) (@hQ e he)).
Qed.
End SmoothedKernelIntegralFamily.
