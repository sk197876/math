(** Federer (1969), 4.1.4, p. 349: the actual smoothed
    dual field is constant on every original inner component.
    This assembles the proved norm-smoothness, kernel-support,
    derivative and connectedness results. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws NormRegularity NormRegularityOperations
  NormOpenTopology OpenFamilyTopologyUP ContinuousDualUP ContinuousDualNorm ContinuousMultilinearSealed
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm HilbertFormCompactness
  SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothTestSpaces SmoothTestTopology
  TranslatedKernelTestUP TranslatedKernelTestSealed SmoothedDistributionDensityUP
  SmoothedDistributionDensityExistence SmoothedDistributionDensityContinuity SmoothedDistributionDensityDirectional
  CompactScalarKernelDirectional CoordinateClassSuccessor
  SmoothFunctionSupport SmoothTestEvaluation DistributionDirectionalDerivative InnerParallelFamilyUP InnerComponentFamilyUP InnerComponentFamilyLaws
  SmoothedDistributionInwardDerivativeZero SmoothedDistributionDensitySmoothness ConnectedZeroCoordinateQuotients.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SmoothedDistributionInnerConstancy.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
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
Variable T:Hom DT R^o.
Hypothesis hT:open_family_continuous (smooth_test_opens hE hD)
  (norm_open_family hNS) T.
Variable YD:lmodType R.
Variable ed:Hom YD (Hom Y R^o).
Variable DN:YD->R.
Hypothesis hYD:is_continuous_dual hNY ed DN.
Local Notation hDN := (continuous_dual_norm_is_norm hYD).


Variable psi:X->R.
Hypothesis hPsi:norm_class_all_orders hN hNS (fun _=>True) psi.
Variable r:R.
Hypothesis hOff:forall x,r<N x ->psi x=0.
Variable B:X->Hom Y DT.
Hypothesis hB:@is_translated_kernel_tests R X Y N NY hN hNY E ev hE psi B.
Variable g:X->YD.
Hypothesis hg:is_smoothed_distribution_density B T ed g.
Variable A:set X.
Variable O:R->set X.
Hypothesis hO:is_inner_parallel_family N A O.
Variable a:X.
Variable C:R->set X.
Hypothesis hC:@is_inner_component_family R (real_norm_metric_space hN) O a C.
Local Notation hFull := (fun x (_:True)=>norm_full_domain_interior N x).
Hypothesis hAnn:forall i:'I_n,forall f:DT,
  (@smooth_function_support R X Y N hN (fun _=>True) DT (smooth_test_value hE) f `<=` A) ->
  T (@distribution_test_directional_derivative R X Y N NY hN hNY
    (fun _=>True) hFull E ev hE D hD (@coordinate_basis R n i) f)=0.

(** Source for [smoothed_distribution_inner_component_constant]:
    the actual g_e maps each original C_e to a single point
    of Y*, Federer 4.1.4, p. 349. All coordinate derivatives
    are proved zero from the given derivative annihilation;
    no positive dimension or target separability is assumed. *)
Theorem smoothed_distribution_inner_component_constant:0<r ->
  forall u v,C r u ->C r v ->g v=g u.
Proof.
move=>hr.
have hSmooth:=@smoothed_distribution_density_smooth R n Y NY hNY E ev hE D hD
  T hT YD ed DN hYD psi r B g hPsi hOff hB hg.
have hClass:=(@norm_class_firstP R X YD N DN hN hDN (fun _=>True) g).1 (hSmooth 1%N).
apply:(@connected_zero_coordinate_quotients_constant R n YD DN hDN (C r) g hClass
  (@inner_component_open R X N hN A O hO a C hC r hr)
  (@inner_component_connected R X N hN O a C hC r hr)).
move=>x hx i.
have hxO:O r x.
  rewrite (@hC r hr) in hx.
  exact:(@connected_component_sub (real_norm_metric_space hN) (O r) a x hx).
have[theta [G [hTheta [hThetaOff [hG hGV]]]]]:=
  @compact_scalar_kernel_directional_exists R n psi r (@coordinate_basis R n i) hPsi hOff.
pose CTest:=@TranslatedKernelTest.value R n Y NY hNY E ev hE theta hTheta r hThetaOff.
pose hCTest:=@TranslatedKernelTest.laws R n Y NY hNY E ev hE theta hTheta r hThetaOff.
have[q hq]:=@smoothed_distribution_density_exists R n Y NY hNY E ev hE D hD
  theta hTheta r hThetaOff CTest hCTest T hT YD ed DN hYD.
exact:(@smoothed_distribution_inward_derivative_zero R n Y NY hNY E ev hE D hD
  psi hPsi r hOff B hB T hT YD ed DN hYD g hg (@coordinate_basis R n i)
  theta G hG hGV hThetaOff CTest hCTest q hq A O hO hr (@hAnn i) x hxO).
Qed.
End SmoothedDistributionInnerConstancy.
