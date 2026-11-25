(** Federer (1969), 4.1.4, p. 349: the family of
    actual smooth dual densities associated with the original
    normalized dilated kernels. Evaluation laws are stated
    independently of the existence proof. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws NormRegularity NormRegularityOperations
  NormOpenTopology OpenFamilyTopologyUP ContinuousDualUP ContinuousDualNorm ContinuousMultilinearSealed
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm HilbertFormCompactness
  SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothTestSpaces SmoothTestTopology
  TranslatedKernelTestUP TranslatedKernelTestSealed SmoothedDistributionDensityUP
  SmoothedDistributionDensityExistence SmoothedDistributionDensityContinuity SmoothedDistributionDensityDirectional
  CompactScalarKernelDirectional CoordinateClassSuccessor
  SmoothFunctionSupport SmoothTestEvaluation DistributionDirectionalDerivative InnerParallelFamilyUP InnerComponentFamilyUP InnerComponentFamilyLaws
  SmoothedDistributionInwardDerivativeZero SmoothedDistributionDensitySmoothness ConnectedZeroCoordinateQuotients
  SmoothingKernelUP SmoothingDilationUP SmoothingDilationSmooth SmoothingDilationNonzeroRadius.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SmoothedKernelDensityFamily.
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



Variable family:R->X->R.

(** Source for [is_smoothed_kernel_density_family]: the original
    positive-scale kernel tests and dual densities from 4.1.2,
    used simultaneously in the proof of Federer 4.1.4, p. 349.
    Only their original evaluation laws are specified. *)
Definition is_smoothed_kernel_density_family
    (B:R->X->Hom Y DT) (g:R->X->YD):Prop:=
  forall e:R,0<e ->
    @is_translated_kernel_tests R X Y N NY hN hNY E ev hE (family e) (B e) /\
    is_smoothed_distribution_density (B e) T ed (g e).

(** Source for [smoothed_kernel_density_family_exists]: the
    actual kernel tests and dual densities used in both
    positive limits of Federer 4.1.4, p. 349, exist at all
    positive scales. Each individual test and density uses
    the previously proved existence and sealed test operator. *)
Theorem smoothed_kernel_density_family_exists (phi:X->R):
  is_smoothing_kernel phi ->is_smoothing_dilation phi family ->
  exists B:R->X->Hom Y DT,exists g:R->X->YD,
    is_smoothed_kernel_density_family B g.
Proof.
move=>hPhi hFamily.
have hFor e:exists p:((X->Hom Y DT)*(X->YD))%type,
    0<e ->@is_translated_kernel_tests R X Y N NY hN hNY E ev hE (family e) p.1 /\
      is_smoothed_distribution_density p.1 T ed p.2.
  case:(pselect (0<e))=>he.
  - pose hSmooth:=@smoothing_dilation_smooth R n phi hPhi family hFamily e he.
    pose hOff:=@smoothing_dilation_zero_beyond_radius R n phi family hPhi hFamily e he.
    pose B:=@TranslatedKernelTest.value R n Y NY hNY E ev hE (family e) hSmooth e hOff.
    pose hB:=@TranslatedKernelTest.laws R n Y NY hNY E ev hE (family e) hSmooth e hOff.
    have[g hg]:=@smoothed_distribution_density_exists R n Y NY hNY E ev hE D hD
      (family e) hSmooth e hOff B hB T hT YD ed DN hYD.
    exists (B,g); move=>_; by split.
  - exists ((fun _=>0),(fun _=>0)); by move=>/he.
have[p hp]:=choice hFor.
exists (fun e=>(p e).1),(fun e=>(p e).2).
exact hp.
Qed.
End SmoothedKernelDensityFamily.
