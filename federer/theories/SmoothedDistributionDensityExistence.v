(** Federer (1969), 4.1.2, p. 347: the
    translated kernel evaluations are actual members of
    the continuous dual Y*. The distribution bound
    proves their continuity before any density is selected. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws NormRegularity NormOpenTopology
  OpenFamilyTopologyUP ContinuousRealFunctional ContinuousDualUP ContinuousMultilinearSealed
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm HilbertFormCompactness FiniteNormEquivalence
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSupport SmoothFunctionDerivativesUP SmoothFunctionTopology
  SmoothTestSpaces SmoothTestEvaluation SmoothTestTopology DistributionSupportedBound
  TranslatedKernelTestUP TranslatedKernelTestSeminormBound SmoothedDistributionDensityUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section SmoothedDistributionDensityExistence.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
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
Hypothesis hPsi:norm_class_all_orders hN (@scalar_absolute_value_norm R) (fun _=>True) psi.
Variable r:R.
Hypothesis hOff:forall x,r<N x ->psi x=0.
Variable B:X->Hom Y DT.
Hypothesis hB:@is_translated_kernel_tests R X Y N NY hN hNY E ev hE psi B.
Variable T:Hom DT R^o.
Hypothesis hT:open_family_continuous (smooth_test_opens hE hD)
  (norm_open_family (@scalar_absolute_value_norm R)) T.
Variable YD:lmodType R.
Variable ed:Hom YD (Hom Y R^o).
Variable DN:YD->R.
Hypothesis hYD:is_continuous_dual hNY ed DN.

(** Source for [smoothed_distribution_density_at_exists]: every
    displayed evaluation of g_epsilon is a bounded
    linear functional on Y, as asserted in
    Federer 4.1.2, p. 347. *)
Theorem smoothed_distribution_density_at_exists z:
  exists a:YD,forall y,ed a y=T (B z y).
Proof.
pose K:=@Build_smooth_compact_set R X N hN (fun _=>True) [set x|N (x-z)<=r]
  (fun _ _=>Logic.I)
  (@finite_norm_closed_ball_compact R X n (@coordinate_basis R n) (@coordinate_basisP R n) N hN z r).
have hSupport y:@smooth_function_support R X Y N hN (fun _=>True) E ev
    (smooth_test_inclusion hE (B z y)) `<=` smooth_compact_carrier K.
  apply:(smooth_function_compact_support_iff hE K _).2=>x hx.
  change (smooth_test_value hE (B z y) x=0).
  rewrite hB.
  have hLarge:r<N (x-z) by rewrite ltNge; apply/negP=>hSmall; apply:hx.
  by rewrite (@hOff (x-z) hLarge) scale0r.
have[i [M hBound]]:=@distribution_supported_local_bound R X Y N NY hN hNY
  (fun _=>True) (fun x _=>norm_full_domain_interior N x) E ev hE D hD T hT K.
have[C [hC hNu]]:=@translated_kernel_test_seminorm_bound R n Y NY hNY E ev hE D hD
  psi hPsi r hOff B hB z i K.
pose L:=hom_comp T (B z).
have hMC:0<=M%:R*C:=mulr_ge0 (ler0n R M) hC.
have hEval y:`|hom_as_linear L y|<=(M%:R*C)*NY y.
  change (`|T (B z y)|<=(M%:R*C)*NY y).
  apply:le_trans (hBound (B z y) (hSupport y)) _.
  have h:=ler_wpM2l (ler0n R M) (hNu y).
  by rewrite mulrA in h.
have hContinuous:=@bounded_real_functional_continuous R Y NY hNY (hom_as_linear L)
  (M%:R*C) hMC hEval.
have[a ha]:=continuous_dual_surjective hYD hContinuous.
exists a=>y; by rewrite ha hom_compE.
Qed.

(** Source for [smoothed_distribution_density_exists]: the original
    displayed dual-valued field in Federer 4.1.2,
    p. 347, exists with all its actual pairings. *)
Theorem smoothed_distribution_density_exists:
  exists g:X->YD,is_smoothed_distribution_density B T ed g.
Proof.
have[g hg]:=choice smoothed_distribution_density_at_exists.
exists g; exact hg.
Qed.
End SmoothedDistributionDensityExistence.
