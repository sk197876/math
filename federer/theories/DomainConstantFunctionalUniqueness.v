(** Federer (1969), 4.1.4, pp. 348–349: constants
    representing the same distribution agree on overlapping
    nonempty open domains. The original normalized kernel
    test and fixed-support zero-extension inverse prove this
    localization inference, including dimension zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology lra.
From Federer Require Import Hom RealNormUP NormMetric CompleteMetricUP NormDifferentialUP NormOpenDomainLaws
  ContinuousRealFunctional GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  SmoothFunctionSpaceUP SmoothFunctionSpaceSealed SmoothFunctionSupport SmoothTestSpaces SmoothTestEvaluation
  TestZeroExtensionSealed TestZeroExtensionLaws TestZeroExtensionRange
  SmoothingKernelSealed SmoothingDilationSealed SmoothingDilationSmooth SmoothingDilationIntegral SmoothingDilationNonzeroRadius
  TranslatedKernelTestSealed TranslatedKernelExactSupport TranslatedKernelUnitMass
  InnerParallelFamilySealed InnerParallelFamilyLaws VectorIntegralTotalEvaluation
  MeasureIntegralUP SummableRealFunctionUP MeasureVectorIntegralUP PartialFunctionBasic EuclideanLebesgueDimensions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section DomainConstantFunctionalUniqueness.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Hypothesis hY:is_complete_metric_space (real_norm_metric_space hNY).
Variable U:set X.
Hypothesis hU:forall x,U x ->norm_domain_interior N U x.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hN hNY U ev.
Local Notation DT := (smooth_test_space hE).
Local Notation value := (smooth_test_value hE).
Local Notation support := (@smooth_function_support R X Y N hN U DT value).
Variable A:set X.
Hypothesis hOpen:@open (real_norm_metric_space hN) A.
Hypothesis hAU:A `<=` U.
Variable a:X.
Hypothesis ha:A a.
Variable T:Hom DT R^o.
Variables alpha beta:Hom Y R^o.
Hypothesis hAlpha:is_continuous_real_functional hNY (hom_as_linear alpha).
Hypothesis hBeta:is_continuous_real_functional hNY (hom_as_linear beta).
Hypothesis hRepAlpha:forall f:DT,support f `<=` A ->
  is_measure_integral (@euclidean_lebesgue_measure R n) (real_total_integrand (fun x=>alpha (value f x))) (T f)%:E.
Hypothesis hRepBeta:forall f:DT,support f `<=` A ->
  is_measure_integral (@euclidean_lebesgue_measure R n) (real_total_integrand (fun x=>beta (value f x))) (T f)%:E.

(** Source for [domain_constant_functional_unique]: the local
    representing functional is unique on every nonempty open
    domain, the overlap inference in the initial reduction
    and fixed-test argument of Federer 4.1.4, pp. 348–349. *)
Theorem domain_constant_functional_unique:alpha=beta.
Proof.
pose hFull:=fun x (_:True)=>norm_full_domain_interior N x.
pose B:=@SmoothFunctionSpace.space R X Y N NY hN hNY (fun _=>True) hFull.
pose bv:=@SmoothFunctionSpace.value R X Y N NY hN hNY (fun _=>True) hFull.
pose hB:=@SmoothFunctionSpace.laws R X Y N NY hN hNY (fun _=>True) hFull.
pose TB:=smooth_test_space hB.
pose valueB:=smooth_test_value hB.
pose supportB:=@smooth_function_support R X Y N hN (fun _=>True) TB valueB.
pose L:=@TestZeroExtension.operator R X Y N NY hN hNY U (fun _=>True) hFull (fun _ _=>Logic.I) E B ev bv hE hB.
pose hL:=@TestZeroExtension.laws R X Y N NY hN hNY U (fun _=>True) hFull (fun _ _=>Logic.I) E B ev bv hE hB.
pose O:=@InnerParallelFamily.value R X N A.
pose hO:=@InnerParallelFamily.laws R X N A.
have[r [hr hSmall]]:=@inner_parallel_eventually_contains R X N hN A O hO hOpen a ha.
have hd:0<r/2 by lra.
have hdr:r/2<r by lra.
have hCentre:O (r/2) a:=@hSmall (r/2) hd hdr.
pose phi:=@SmoothingKernel.value R n.
pose hPhi:=@SmoothingKernel.laws R n.
pose family:=@SmoothingDilation.value R n phi.
pose hFamily:=@SmoothingDilation.laws R n phi.
pose psi:=family (r/2).
pose hSmooth:=@smoothing_dilation_smooth R n phi hPhi family hFamily (r/2) hd.
pose hOff:=@smoothing_dilation_zero_beyond_radius R n phi family hPhi hFamily (r/2) hd.
pose hUnit:=@smoothing_dilation_integral_one R n phi family hPhi hFamily (r/2) hd.
pose BG:=@TranslatedKernelTest.value R n Y NY hNY B bv hB psi hSmooth (r/2) hOff.
pose hBG:=@TranslatedKernelTest.laws R n Y NY hNY B bv hB psi hSmooth (r/2) hOff.
apply:hom_ext=>y.
have hSupport:supportB (BG a y) `<=` A.
  exact:(@translated_kernel_test_inward_support R n Y NY hNY B bv hB psi (r/2) hOff BG hBG
    A O hO hd a hCentre y).
have hInside:supportB (BG a y) `<=` U.
  move=>x hx; exact:(@hAU x (hSupport x hx)).
have[f hF]:=@test_zero_extension_range R X Y N NY hN hNY U (fun _=>True) hU (fun _ _=>Logic.I)
  E B ev bv hE hB L hL (BG a y) hInside.
have hSupportF:support f `<=` A.
  have hSuppEq:=@test_zero_extension_support R X Y N NY hN hNY U (fun _=>True) (fun _ _=>Logic.I)
    E B ev bv hE hB L hL f.
  rewrite hF in hSuppEq.
  by rewrite -hSuppEq.
have hVector:=@translated_kernel_test_unit_integral R n Y NY hNY hY B bv hB psi hSmooth
  (r/2) hOff hUnit BG hBG a y.
have hValues:(fun x=>(value f x:real_norm_metric_space hNY))=
    (fun x=>(valueB (BG a y) x:real_norm_metric_space hNY)).
  apply:funext=>x.
  rewrite -(@test_zero_extension_value R X Y N NY hN hNY U (fun _=>True)
    E B ev bv hE hB L hL f x).
  by rewrite hF.
rewrite -hValues in hVector.
have hAV:=@vector_total_integral_functional_value R X Y NY hNY (@euclidean_lebesgue_measure R n)
  (value f) y alpha (T f) hVector hAlpha (@hRepAlpha f hSupportF).
have hBV:=@vector_total_integral_functional_value R X Y NY hNY (@euclidean_lebesgue_measure R n)
  (value f) y beta (T f) hVector hBeta (@hRepBeta f hSupportF).
exact:etrans (esym hAV) hBV.
Qed.
End DomainConstantFunctionalUniqueness.
