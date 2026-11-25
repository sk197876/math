(** Federer (1969), 4.1.4, pp. 348–349: the original
    global-domain distribution constancy theorem, proved by
    the actual normalized smoothing and fixed unit-mass test.
    The target is an arbitrary Banach space and n may be zero. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom ModuleQuotient NormOpenTopology OpenFamilyTopologyUP MetricClosedBalls RealNormUP NormMetric CompleteMetricUP VectorDaniellHypotheses
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm HilbertFormCompactness ContinuousMultilinearSealed
  LinearSubspaceRepresentationUP SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSupport SmoothFunctionDerivativesUP
  SmoothFunctionTopology SmoothTestEvaluation SmoothTestSpaces SmoothTestTopology SmoothingKernelUP SmoothingDilationUP
  SmoothSmoothingFamilyUP SmoothSmoothingSupport SmoothSmoothingConvergence
  SmoothSupportedPositiveLimit TestSmoothingFamilyUP ContinuousTestSmoothingConvergence
  SmoothFunctionSpaceSealed SmoothFunctionDerivativesSealed SmoothGlobalTranslationSealed NormOpenDomainLaws
  EuclideanLebesgueDimensions ContinuousDualUP SmoothingDilationSmooth SmoothingDilationNonzeroRadius SmoothedKernelDensityFamily
  ContinuousDistributionIntegralAction DistributionIntegralFieldUP
  DistributionDirectionalDerivative ContinuousRealFunctional ContinuousDualSealed SmoothingKernelSealed SmoothingDilationSealed
  ContinuousSmoothSmoothingExistence TestSmoothingFamilyExistence SmoothedDistributionInnerConstancy
  InnerParallelFamilySealed InnerComponentFamilySealed RegularisationConstantRepresentation
  SmoothedKernelIntegralFamily ContinuousDistributionTestLimit PositiveNormLimitUP SummableRealFunctionUP MeasureIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section GlobalDistributionConstancy.
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

Variable T:Hom DT R^o.
Hypothesis hT:open_family_continuous SO (norm_open_family (@scalar_absolute_value_norm R)) T.
Variable A:set X.
Hypothesis hOpen:@open (real_norm_metric_space hN) A.
Hypothesis hConnected:@connected (real_norm_metric_space hN) A.
Variable a:X.
Hypothesis ha:A a.
Local Notation hFull := (fun x (_:True)=>norm_full_domain_interior N x).
Hypothesis hAnn:forall i:'I_n,forall f:DT,
  (@smooth_function_support R X Y N hN (fun _=>True) DT (smooth_test_value hE) f `<=` A) ->
  T (@distribution_test_directional_derivative R X Y N NY hN hNY
    (fun _=>True) hFull E ev hE D hD (@coordinate_basis R n i) f)=0.

(** Source for [global_distribution_annihilating_derivatives_constant]:
    the global-domain constancy theorem in the original proof
    of Federer 4.1.4, pp. 348–349. Every kernel, density,
    convolution, original test limit and constant is supplied
    by its proved existence and public laws. *)
Theorem global_distribution_annihilating_derivatives_constant:
  exists alpha:Hom Y R^o,
    is_continuous_real_functional hNY (hom_as_linear alpha) /\
    forall f:DT,
      (@smooth_function_support R X Y N hN (fun _=>True) DT (smooth_test_value hE) f `<=` A) ->
      is_measure_integral (@euclidean_lebesgue_measure R n)
        (real_total_integrand (fun x=>alpha (smooth_test_value hE f x))) (T f)%:E.
Proof.
pose phi:=@SmoothingKernel.value R n.
pose hPhi:=@SmoothingKernel.laws R n.
pose family:=@SmoothingDilation.value R n phi.
pose hFamily:=@SmoothingDilation.laws R n phi.
have[P hP]:=@continuous_smooth_smoothing_family_exists R n Y NY hNY hY E ev hE
  phi hPhi family hFamily.
have[Q hQ]:=@test_smoothing_family_exists R n Y NY hNY E ev hE phi hPhi family hFamily P hP.
pose YD:=@ContinuousDual.space R Y NY hNY.
pose ed:=@ContinuousDual.evaluation R Y NY hNY.
pose DN:=@ContinuousDual.norm R Y NY hNY.
pose hYD:=@ContinuousDual.laws R Y NY hNY.
have[B [g hBG]]:=@smoothed_kernel_density_family_exists R n Y NY hNY E ev hE D hD
  T hT YD ed DN hYD family phi hPhi hFamily.
pose O:=@InnerParallelFamily.value R X N A.
pose hO:=@InnerParallelFamily.laws R X N A.
pose C:=@InnerComponentFamily.value R (real_norm_metric_space hN) O a.
pose hC:=@InnerComponentFamily.laws R (real_norm_metric_space hN) O a.
have hAction:forall e:R,0<e ->
    is_distribution_integral_action (@euclidean_lebesgue_measure R n) ed (g e)
      (smooth_test_value hE) (hom_comp T (Q e)).
  exact:(@smoothed_kernel_density_integral_action R n Y NY hNY hY E ev hE D hD
    phi hPhi family hFamily P hP Q hQ T hT YD ed DN hYD B g hBG).
have hConst:forall e:R,0<e ->forall u v,C e u ->C e v ->g e v=g e u.
  move=>e he.
  have[hB hg]:=@hBG e he.
  exact:(@smoothed_distribution_inner_component_constant R n Y NY hNY E ev hE D hD
    T hT YD ed DN hYD (family e) (@smoothing_dilation_smooth R n phi hPhi family hFamily e he)
    e (@smoothing_dilation_zero_beyond_radius R n phi family hPhi hFamily e he)
    (B e) hB (g e) hg A O hO a C hC hAnn he).
have hLimit:forall f:DT,positive_norm_limit (fun t:R^o=>`|t|) (fun e=>T (Q e f)) (T f).
  move=>f eta hEta.
  exact:(@continuous_distribution_smoothing_test_limit R n Y NY hNY hY E ev hE D hD
    phi hPhi family hFamily P hP Q hQ T hT f eta hEta).
exact:(@regularisation_constant_scalar_integral R n Y NY hNY hY E ev hE T Q YD ed DN hYD
  g hAction A hOpen hConnected O hO a ha C hC hConst phi hPhi family hFamily B hBG hLimit).
Qed.
End GlobalDistributionConstancy.
