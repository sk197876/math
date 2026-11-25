(** Federer (1969), 4.1.2, p. 347: the
    original smoothed evaluations T(Phi_epsilon*f) converge
    to T(f) for every actual test. Continuity of T
    and the original test-topology convergence suffice. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom ModuleQuotient NormDifferentialUP NormOpenTopology OpenFamilyTopologyUP MetricClosedBalls RealNormUP NormMetric CompleteMetricUP VectorDaniellHypotheses
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness ContinuousMultilinearSealed
  LinearSubspaceRepresentationUP SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSupport SmoothFunctionDerivativesUP
  SmoothFunctionTopology SmoothTestSpaces SmoothTestTopology SmoothingKernelUP SmoothingDilationUP
  SmoothSmoothingFamilyUP SmoothSmoothingSupport SmoothSmoothingConvergence
  SmoothSupportedPositiveLimit TestSmoothingFamilyUP TestSmoothingConvergence
  TestCutoffExhaustionUP FiniteCoordinates SmoothCompactInteriorThickening SmoothCompactCutoffUP SmoothCompactCutoffSealed
  SmoothCutoffReplacement SmoothMultiplierUP SmoothMultiplierSealed
  SmoothRestrictionUP SmoothRestrictionSealed SmoothRestrictionContinuity
  SmoothTestEvaluation SmoothFunctionSupport TestZeroExtensionUP TestZeroExtensionLaws
  EuclideanLebesgueDimensions SmoothingDilationNonzeroRadius CompactConvolutionSupport TestCutoffExhaustionExistence
  NormOpenDomainLaws TestZeroExtensionContinuity ContinuousRealDual ContinuousRealDualTranspose
  SmoothTestScalarMultiplier TestCutoffExtensionFamily SmoothedDistributionFamilyUP
  SmoothedDistributionFamilyExistence LocalizedSmoothingWeakLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ArbitraryOpenSmoothing.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable Y:lmodType R.
Variable NY:Y->R.
Hypothesis hNY:is_real_norm NY.
Hypothesis hY:is_complete_metric_space (real_norm_metric_space hNY).
Hypothesis hSep:is_separable_normed_space hNY.
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



Variable U:set X.
Hypothesis hU:forall x,U x ->norm_domain_interior N U x.
Variable A:lmodType R.
Variable av:A->X->Y.
Hypothesis hA:is_smooth_function_space hN hNY U av.
Variable DA:forall j,X->Hom A (Z j).
Hypothesis hDA:@is_smooth_function_derivatives R X Y N NY hN hNY U A av DA.
Local Notation TA := (smooth_test_space hA).
Local Notation SA := (smooth_test_opens hA hDA).
Variable S0:lmodType R.
Variable sv:S0->X->R^o.
Hypothesis hS0:is_smooth_function_space hN (@scalar_absolute_value_norm R) U sv.

Local Notation hSA := (smooth_test_final_topology_laws hA hDA).1.
Local Notation hSE := (smooth_test_final_topology_laws hE hD).1.
Local Notation DDA := (@continuous_real_dual_space R TA SA hSA).
Local Notation DDE := (@continuous_real_dual_space R DT SO hSE).
Local Notation eA := (@continuous_real_dual_evaluation R TA SA hSA).
Local Notation eE := (@continuous_real_dual_evaluation R DT SO hSE).
Local Notation DOA := (@continuous_real_dual_weak_opens R TA SA hSA).
Variable L:Hom TA DT.
Hypothesis hL:is_test_zero_extension U (fun _=>True) (smooth_test_value hA) (smooth_test_value hE) L.
Variable T:DDA.
Local Notation hFull := (fun x (_:True)=>norm_full_domain_interior N x).
Local Notation hUV := (fun x (_:U x)=>Logic.I).
Local Notation hLC := (@test_zero_extension_continuous R X Y N NY hN hNY U (fun _=>True)
  hU hFull hUV A E av ev hA hE DA D hDA hD L hL).
Local Notation rhoD := (@continuous_real_dual_transpose R TA DT SA SO hSA hSE L hLC).

(** Source for [arbitrary_open_smoothing_exists]: the complete
    arbitrary-open regularisation assertion at the end of Federer
    4.1.2, p. 348. The actual test cutoff sequence, its global
    distribution extensions and their actual smoothing families all
    exist. One large-index and small-radius pair works simultaneously
    in every original weak neighbourhood after restriction to U. *)
Theorem arbitrary_open_smoothing_exists:
  exists omega:nat->smooth_test_space hS0,
  exists S:nat->DDE,exists B:nat->R->DDE,
    @is_test_cutoff_exhaustion R X N hN U S0 sv hS0 omega /\
    (forall j f,eA (rhoD (S j)) f=eA T
      (@smooth_test_scalar_multiplier R X Y N NY hN hNY U A av hA
        (smooth_test_value hS0 (omega j)) (smooth_test_value_smooth hS0 (omega j)) f)) /\
    (forall j,is_smoothed_distribution_family eE (eE (S j)) Q (B j)) /\
    (forall V,DOA V ->V T ->exists v:nat,exists d:R,0<d /\
      forall j,(v<=j)%N ->forall e:R,0<e ->e<d ->V (rhoD (B j e))).
Proof.
have[omega hOmega]:=@test_cutoff_exhaustion_exists R X N hN n (@coordinate_basis R n)
  (@coordinate_basisP R n) U hU S0 sv hS0.
pose hT:=@continuous_real_dual_member_continuous R TA SA hSA T.
have[M [S [hMC [hMV hS]]]]:=@test_cutoff_extension_family_exists R X Y N NY hN hNY
  U hU A E av ev hA hE DA D hDA hD S0 sv hS0 omega (eA T) hT.
have hForFamily j:exists b:R->DDE,is_smoothed_distribution_family eE (eE (S j)) Q b.
  exact:(@smoothed_distribution_family_exists R n Y NY hNY hY hSep E ev hE D hD
    phi hPhi family hFamily P hP Q hQ (eE (S j))
    (@continuous_real_dual_member_continuous R DT SO hSE (S j))).
have[B hB]:=choice hForFamily.
have hRho G f:eA (rhoD G) f=eE G (L f).
  exact:(@continuous_real_dual_transpose_evaluation R TA DT SA SO hSA hSE L hLC G f).
have hOriginal j f:
    eA (rhoD (S j)) f=eA T
      (@smooth_test_scalar_multiplier R X Y N NY hN hNY U A av hA
        (smooth_test_value hS0 (omega j)) (smooth_test_value_smooth hS0 (omega j)) f).
  rewrite hRho hS; congr (eA T _).
  apply:(smooth_test_values_extensional hA)=>x hx.
  rewrite hMV // smooth_test_scalar_multiplier_value //.
  change (smooth_test_value hS0 (omega j) x*:smooth_test_value hE (L f) x=
    smooth_test_value hS0 (omega j) x*:smooth_test_value hA f x).
  by rewrite (@test_zero_extension_original R X Y TA DT U (fun _=>True)
    (smooth_test_value hA) (smooth_test_value hE) L hL f x hx).
exists omega,S,B; split; first exact hOmega.
split; first exact hOriginal.
split; first exact hB.
move=>V hV hVT.
exact:(@localized_smoothing_weak_limit R n Y NY hNY hY hSep E ev hE D hD
  phi hPhi family hFamily P hP Q hQ U hU A av hA DA hDA S0 sv hS0
  omega hOmega L hL (eA T) hT M hMV T (erefl _) S hS B hB rhoD hRho V hV hVT).
Qed.
End ArbitraryOpenSmoothing.
