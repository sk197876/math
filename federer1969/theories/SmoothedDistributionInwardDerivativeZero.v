(** Federer (1969), 4.1.4, p. 349: locality of the
    distribution derivative makes the actual smoothed dual
    density derivative zero at every original inward point.
    Kernel tests and their derivatives are the actual sealed
    test-space operators from 4.1.1 and 4.1.2. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology lra.
From Federer Require Import Hom ModuleQuotient RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  NormClassOneUP NormedCurveDerivativeUP NormRegularity NormOpenTopology OpenFamilyTopologyUP ContinuousDualUP ContinuousMultilinearSealed
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSpaceLaws SmoothFunctionSpaceSealed SmoothFunctionSupport
  SmoothFunctionDerivativesUP SmoothFunctionDerivativesSealed SmoothFunctionTopology SmoothDerivativeSeminormUP
  SmoothTestSubspaces SmoothTestSpaces SmoothTestEvaluation SmoothTestTopology
  SmoothGlobalTranslationUP SmoothGlobalTranslationSealed SmoothDirectionalDerivativeUP SmoothDirectionalDerivativeSealed
  SmoothDifferenceQuotientJets SmoothDifferenceQuotientSeminorm SmoothTranslatedOrdinary
  TranslatedKernelTestUP TranslatedKernelTestCommonSupport DistributionTensorDualBound SmoothedDistributionDensityUP
  TestDirectionalOperator DistributionDirectionalDerivative TranslatedKernelTestDirectional TranslatedKernelExactSupport
  InnerParallelFamilyUP SmoothedDistributionDensityDirectional.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SmoothedDistributionInwardDerivativeZero.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation NS := (fun t:R^o=>`|t|).
Local Notation hNS := (@scalar_absolute_value_norm R).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hN hNY (fun _=>True) ev.
Local Notation Z := (fun j=>@ContinuousMultilinear.space R j X Y N NY hN hNY).
Variable D:forall j,X->Hom E (Z j).
Hypothesis hD:@is_smooth_function_derivatives R X Y N NY hN hNY (fun _=>True) E ev D.
Local Notation DT := (smooth_test_space hE).
Variable psi:X->R.
Hypothesis hPsi:norm_class_all_orders hN hNS (fun _=>True) psi.
Variable r:R.
Hypothesis hOff:forall x,r<N x ->psi x=0.
Variable B:X->Hom Y DT.
Hypothesis hB:@is_translated_kernel_tests R X Y N NY hN hNY E ev hE psi B.
Variable T:Hom DT R^o.
Hypothesis hT:open_family_continuous (smooth_test_opens hE hD)
  (norm_open_family hNS) T.
Variable YD:lmodType R.
Variable ed:Hom YD (Hom Y R^o).
Variable DN:YD->R.
Hypothesis hYD:is_continuous_dual hNY ed DN.
Variable g:X->YD.
Hypothesis hg:is_smoothed_distribution_density B T ed g.


Variable v:X.
Variable theta:X->R.
Variable G:X->Hom X R^o.
Hypothesis hG:forall x,has_norm_differential N NS (fun _=>True) psi x (G x).
Hypothesis hTheta:forall x,G x v=theta x.
Hypothesis hThetaOff:forall x,r<N x ->theta x=0.
Variable CTest:X->Hom Y DT.
Hypothesis hCTest:@is_translated_kernel_tests R X Y N NY hN hNY E ev hE theta CTest.
Variable q:X->YD.
Hypothesis hq:is_smoothed_distribution_density CTest T ed q.


Variable A:set X.
Variable O:R->set X.
Hypothesis hO:is_inner_parallel_family N A O.
Hypothesis hr:0<r.
Local Notation hFull := (fun x (_:True)=>norm_full_domain_interior N x).
Local Notation DP := (@distribution_test_directional_derivative R X Y N NY hN hNY
  (fun _=>True) hFull E ev hE D hD v).
Hypothesis hAnn:forall f:DT,
  (@smooth_function_support R X Y N hN (fun _=>True) DT (smooth_test_value hE) f `<=` A) ->T (DP f)=0.

(** Source for [smoothed_distribution_inward_derivative_zero]:
    D_v g_e(z)=0 whenever the original radius-e kernel lies
    inside A and D_v T annihilates tests supported in A,
    the calculation in Federer 4.1.4, p. 349. The derivative
    is in the full continuous-dual norm. *)
Theorem smoothed_distribution_inward_derivative_zero z:O r z ->
  punctured_norm_limit DN (fun t=>t^-1*:(g (z+t*:v)-g z)) 0.
Proof.
move=>hz.
pose S:=@SmoothFunctionSpace.space R X R^o N NS hN hNS (fun _=>True) hFull.
pose sv:=@SmoothFunctionSpace.value R X R^o N NS hN hNS (fun _=>True) hFull.
pose hS:=@SmoothFunctionSpace.laws R X R^o N NS hN hNS (fun _=>True) hFull.
pose DS:=@SmoothFunctionDerivatives.operators R X R^o N NS hN hNS (fun _=>True) S sv hS.
pose hDS:=@SmoothFunctionDerivatives.laws R X R^o N NS hN hNS (fun _=>True) S sv hS.
pose L:=@SmoothGlobalTranslation.operator R X R^o N NS hN hNS S sv hS.
have hL c:=@SmoothGlobalTranslation.laws R X R^o N NS hN hNS S sv hS c.
have[s hs]:=smooth_function_evaluation_surjective hS hPsi.
have hF x:sv s x=psi x:=hs x Logic.I.
pose P:=@SmoothDirectionalDerivative.operator R X Y N NY hN hNY (fun _=>True) E ev hE D hD v.
pose hP:=@SmoothDirectionalDerivative.laws R X Y N NY hN hNY (fun _=>True) E ev hE D hD v.
have hTest z0 y:DP (B z0 y)=CTest z0 y.
  change (@test_directional_operator R X Y N NY hN hNY (fun _=>True) hFull E ev hE D hD v P hP (B z0 y)=CTest z0 y).
  exact:(@translated_kernel_test_directional_derivative R X Y N NY hN hNY
    S sv hS DS hDS L hL s psi hF G hG v theta hTheta E ev hE D hD B CTest hB hCTest P hP z0 y).
have hQZero:q z=0.
  apply:(continuous_dual_injective hYD); apply:hom_ext=>y.
  have hZero:ed (0:YD) y=0 by rewrite linear0 hom_zeroE.
  rewrite hZero hq -hTest.
  apply:hAnn.
  exact:(@translated_kernel_test_inward_support R n Y NY hNY E ev hE psi r hOff B hB
    A O hO hr z hz y).
have hLimit:=@smoothed_distribution_density_directional R n Y NY hNY E ev hE D hD
  psi hPsi r hOff B hB T hT YD ed DN hYD g hg v theta G hG hTheta hThetaOff CTest hCTest q hq z.
by rewrite hQZero oppr0 in hLimit.
Qed.
End SmoothedDistributionInwardDerivativeZero.
