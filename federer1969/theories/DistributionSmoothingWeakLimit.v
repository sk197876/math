(** Federer (1969), 4.1.2, p. 347: the
    original smoothed evaluations T(Phi_epsilon*f) converge
    to T(f) for every actual test. Continuity of T
    and the original test-topology convergence suffice. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom ModuleQuotient NormOpenTopology OpenFamilyTopologyUP MetricClosedBalls RealNormUP NormMetric CompleteMetricUP VectorDaniellHypotheses
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness ContinuousMultilinearSealed
  LinearSubspaceRepresentationUP SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSupport SmoothFunctionDerivativesUP
  SmoothFunctionTopology SmoothTestSpaces SmoothTestTopology SmoothingKernelUP SmoothingDilationUP
  SmoothSmoothingFamilyUP SmoothSmoothingSupport SmoothSmoothingConvergence
  SmoothSupportedPositiveLimit TestSmoothingFamilyUP TestSmoothingConvergence
  ContinuousRealDual WeakEvaluationTopologySealed WeakEvaluationConvergenceUP WeakPositiveParameterLimit
  SmoothedDistributionFamilyUP DistributionSmoothingTestLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section DistributionSmoothingWeakLimit.
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



Local Notation DD := (@continuous_real_dual_space R DT SO (smooth_test_final_topology_laws hE hD).1).
Local Notation eD := (@continuous_real_dual_evaluation R DT SO (smooth_test_final_topology_laws hE hD).1).
Variable T:DD.
Variable A:R->DD.
Hypothesis hA:is_smoothed_distribution_family eD (eD T) Q A.

(** Source for [distribution_smoothing_weak_limit]: the full original
    convergence T_epsilon -> T in D'(R^n,Y), Federer 4.1.2,
    p. 347. Every neighbourhood for the actual weak dual topology
    is attained for all sufficiently small positive parameters. *)
Theorem distribution_smoothing_weak_limit V:
  (@continuous_real_dual_weak_opens R DT SO (smooth_test_final_topology_laws hE hD).1) V ->V T ->
  exists d:R,0<d /\ forall e:R,0<e ->e<d ->V (A e).
Proof.
have hT:=@continuous_real_dual_member_continuous R DT SO
  (smooth_test_final_topology_laws hE hD).1 T.
apply:(@weak_positive_parameter_limit R DT DD (fun a f=>eD a f)
  (@continuous_real_dual_weak_opens R DT SO (smooth_test_final_topology_laws hE hD).1)
  (WeakEvaluationTopology.convergence (fun a f=>eD a f)) A T).
move=>f eta hEta.
have[d [hd hBound]]:=@distribution_smoothing_test_limit R n Y NY hNY hY hSep
  E ev hE D hD phi hPhi family hFamily P hP Q hQ (eD T) hT f eta hEta.
exists d; split=>//e he hSmall.
rewrite (@hA e he f); exact:hBound e he hSmall.
Qed.
End DistributionSmoothingWeakLimit.
