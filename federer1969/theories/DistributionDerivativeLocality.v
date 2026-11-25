(** Federer (1969), 4.1.4, pp. 348–349: the original
    derivative-support hypothesis implies annihilation on A.
    The original functional support theorem and actual
    negative-transpose derivative supply the inference. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity NormRegularityOperations
  LinearBasis CompactSupportFunctionUP SmoothFunctionSpaceUP SmoothFunctionSupport SmoothTestSpaces
  SmoothTestEvaluation SmoothCompactPartitionUP FiniteNormSmoothPartitionExistence
  SmoothPartitionCompactSelection SmoothMultiplierUP SmoothTestScalarMultiplier
  SmoothTestFiniteDecomposition FunctionalSupportUP SmoothTestAnnihilationCover
  SmoothTestFunctionalSupport ContinuousMultilinearSealed SmoothFunctionDerivativesUP SmoothTestTopology
  ContinuousRealDual DistributionDirectionalDerivative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section DistributionDerivativeLocality.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable n:nat.
Variable b:'I_n->X.
Hypothesis hb:is_basis b.
Variable U:set X.
Hypothesis hU:forall x,U x ->norm_domain_interior NX U x.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Local Notation XN := (real_norm_metric_space hNX).
Local Notation DT := (smooth_test_space hE).
Local Notation value := (smooth_test_value hE).
Local Notation support := (@smooth_function_support R X Y NX hNX U DT value).
Local Notation tsupport := (@smooth_functional_support R X Y NX hNX U DT value).


Variable D:forall k,X->Hom E (@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.
Local Notation SO := (smooth_test_opens hE hD).
Local Notation hSO := (smooth_test_final_topology_laws hE hD).1.
Local Notation DD := (@continuous_real_dual_space R DT SO hSO).
Local Notation eD := (@continuous_real_dual_evaluation R DT SO hSO).
Variable T:DD.
Variable v:X.
Variable A:set X.
Local Notation DP := (@distribution_test_directional_derivative R X Y NX NY hNX hNY U hU E ev hE D hD v).
Local Notation DV := (@distribution_directional_derivative R X Y NX NY hNX hNY U hU E ev hE D hD v).
Hypothesis hSupport:forall x,tsupport (eD (DV T)) x ->U x /\ ~A x.

(** Source for [distribution_derivative_support_annihilation]:
    the original support hypothesis spt D_j T contained
    in U minus A makes T annihilate derivatives of all
    tests supported in A, the locality used throughout
    Federer 4.1.4, pp. 348–349. *)
Theorem distribution_derivative_support_annihilation f:
  support f `<=` A ->eD T (DP f)=0.
Proof.
move=>hSupp.
have hDisjoint:forall x,tsupport (eD (DV T)) x ->~support f x.
  move=>x hx hxf; exact:((@hSupport x hx).2 (hSupp x hxf)).
have hZero:=@smooth_test_functional_disjoint_support_zero R X Y NX NY hNX hNY n b hb
  U hU E ev hE (eD (DV T)) f hDisjoint.
rewrite distribution_directional_derivative_evaluation in hZero.
apply:oppr_inj; by rewrite hZero oppr0.
Qed.
End DistributionDerivativeLocality.
