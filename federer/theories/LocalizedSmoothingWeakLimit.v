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
  EuclideanLebesgueDimensions SmoothingDilationNonzeroRadius CompactConvolutionSupport ContinuousRealDual WeakEvaluationTopologySealed
  SmoothedDistributionFamilyUP WeakDirectedPositiveParameterLimit LocalizedSmoothingTestLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section LocalizedSmoothingWeakLimit.
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
Variable omega:nat->smooth_test_space hS0.
Hypothesis hOmega:@is_test_cutoff_exhaustion R X N hN U S0 sv hS0 omega.
Variable L:Hom TA DT.
Hypothesis hL:is_test_zero_extension U (fun _=>True) (smooth_test_value hA) (smooth_test_value hE) L.
Variable T:Hom TA R^o.
Hypothesis hT:open_family_continuous SA (norm_open_family (@scalar_absolute_value_norm R)) T.
Variable M:nat->Hom E TA.
Hypothesis hM:forall j g x,U x ->smooth_test_value hA (M j g) x=
  smooth_test_value hS0 (omega j) x*:ev g x.


Local Notation DDA := (@continuous_real_dual_space R TA SA (smooth_test_final_topology_laws hA hDA).1).
Local Notation eA := (@continuous_real_dual_evaluation R TA SA (smooth_test_final_topology_laws hA hDA).1).
Local Notation DDE := (@continuous_real_dual_space R DT SO (smooth_test_final_topology_laws hE hD).1).
Local Notation eE := (@continuous_real_dual_evaluation R DT SO (smooth_test_final_topology_laws hE hD).1).
Local Notation DOA := (@continuous_real_dual_weak_opens R TA SA (smooth_test_final_topology_laws hA hDA).1).
Variable T0:DDA.
Hypothesis hT0:eA T0=T.
Variable S:nat->DDE.
Hypothesis hS:forall j f,eE (S j) f=T (M j (inc f)).
Variable B:nat->R->DDE.
Hypothesis hB:forall j,is_smoothed_distribution_family eE (eE (S j)) Q (B j).
Variable rhoD:Hom DDE DDA.
Hypothesis hRhoD:forall G f,eA (rhoD G) f=eE G (L f).

(** Source for [localized_smoothing_weak_limit]: the full original
    weak convergence on arbitrary open U at the end of Federer 4.1.2,
    p. 348. The actual global smoothed extensions are restricted to U,
    and a single large-index threshold and small positive radius
    suffice for each original weak neighbourhood. *)
Theorem localized_smoothing_weak_limit V:DOA V ->V T0 ->
  exists v:nat,exists d:R,0<d /\ forall j,(v<=j)%N ->
    forall e:R,0<e ->e<d ->V (rhoD (B j e)).
Proof.
apply:(@weak_directed_positive_parameter_limit R TA DDA (fun G f=>eA G f)
  DOA (WeakEvaluationTopology.convergence (fun G f=>eA G f)) (fun j e=>rhoD (B j e)) T0).
move=>f eta hEta.
have[v [d [hd hBound]]]:=@localized_smoothing_test_limit R n Y NY hNY hY hSep
  E ev hE D hD phi hPhi family hFamily P hP Q hQ U hU A av hA DA hDA
  S0 sv hS0 omega hOmega L hL T hT M hM f eta hEta.
exists v,d; split=>//j hj e he hSmall.
rewrite hRhoD (@hB j e he (L f)) hS hT0.
exact:hBound j hj e he hSmall.
Qed.
End LocalizedSmoothingWeakLimit.
