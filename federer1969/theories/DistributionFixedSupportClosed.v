(** Federer (1969), 4.1.1, pp. 344–345: the
    support condition is a weakly closed condition on
    distributions. This supporting result transfers to the
    printed closed subsets E'_K through the natural map. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP LinearBasis ContinuousMultilinearSealed
  SmoothCompactSet SmoothFunctionSpaceUP SmoothFunctionSupport SmoothFunctionDerivativesUP
  SmoothTestSpaces SmoothTestEvaluation SmoothTestTopology FunctionalSupportUP
  ContinuousRealDual SmoothTestSupportCriterion WeakEvaluationZeroLocus.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section DistributionFixedSupportClosed.
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
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.
Local Notation DT := (smooth_test_space hE).
Local Notation value := (smooth_test_value hE).
Local Notation SO := (smooth_test_opens hE hD).
Local Notation hSO := (smooth_test_final_topology_laws hE hD).1.
Local Notation DD := (@continuous_real_dual_space R DT SO hSO).
Local Notation e := (@continuous_real_dual_evaluation R DT SO hSO).
Local Notation DO := (@continuous_real_dual_weak_opens R DT SO hSO).

(** Source for [distribution_fixed_support_set]: the subset
    of distributions supported in a prescribed compact K,
    supporting the fixed-support comparison in Federer
    4.1.1, p. 345. *)
Definition distribution_fixed_support_set (K:smooth_compact_set hNX U):set DD:=
  [set T|@smooth_functional_support R X Y NX hNX U DT value (e T) `<=` smooth_compact_carrier K].

(** Source for [distribution_fixed_support_weakly_closed]:
    the compact-support containment condition is weakly
    closed, supporting the printed E'_K closedness
    in Federer 4.1.1, p. 344. *)
Theorem distribution_fixed_support_weakly_closed (K:smooth_compact_set hNX U):
  DO (~` distribution_fixed_support_set K).
Proof.
pose I:set DT:=[set f|@smooth_function_support R X Y NX hNX U DT value f `<=`
  (U `&` ~` smooth_compact_carrier K)].
have hClosed:=@weak_evaluation_zero_locus_closed R DT DD (fun T f=>e T f) DO
  (@continuous_real_dual_weak_laws R DT SO hSO) I.
have hEq:distribution_fixed_support_set K=[set T:DD|forall f,I f ->e T f=0].
  apply:funext=>T; apply:propext.
  exact:(@smooth_test_support_compact_criterion R X Y NX NY hNX hNY n b hb U hU E ev hE K (e T)).
by rewrite hEq.
Qed.
End DistributionFixedSupportClosed.
