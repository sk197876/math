(** Federer (1969), 4.1.4, p. 348: actual test
    derivatives are local and retain the original support.
    The public first-differential and compact-support laws
    of 4.1.1 supply these localization adapters. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP ContinuousMultilinearSealed
  OpenFamilyTopologyUP SmoothFunctionSpaceUP SmoothFunctionDerivativesUP
  SmoothDirectionalDerivativeSealed SmoothTestSpaces SmoothTestTopology TestDirectionalOperator
  ContinuousRealDual ContinuousRealDualScaledTranspose DistributionDirectionalDerivative
  ModuleQuotient SmoothCompactSet SmoothFunctionSupport SmoothTestEvaluation SmoothDirectionalSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section TestDirectionalValues.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable U:set X.
Hypothesis hU:forall x,U x -> norm_domain_interior NX U x.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.
Variable v:X.
Local Notation P := (@SmoothDirectionalDerivative.operator R X Y NX NY hNX hNY U E ev hE D hD v).
Local Notation hP := (@SmoothDirectionalDerivative.laws R X Y NX NY hNX hNY U E ev hE D hD v).
Local Notation DT := (smooth_test_space hE).
Local Notation SO := (smooth_test_opens hE hD).
Local Notation hSO := (smooth_test_final_topology_laws hE hD).1.
Local Notation DD := (@continuous_real_dual_space R DT SO hSO).
Local Notation e := (@continuous_real_dual_evaluation R DT SO hSO).
Local Notation DO := (@continuous_real_dual_weak_opens R DT SO hSO).
Local Notation TOp := (@test_directional_operator R X Y NX NY hNX hNY U hU E ev hE D hD v P hP).
Local Notation hTOp := (@test_directional_operator_continuous R X Y NX NY hNX hNY U hU E ev hE D hD v P hP).


Local Notation DP := (@distribution_test_directional_derivative R X Y NX NY hNX hNY U hU E ev hE D hD v).
Local Notation support := (@smooth_function_support R X Y NX hNX U DT (smooth_test_value hE)).

(** Source for [distribution_test_directional_derivative_value]:
    the actual test derivative has its original first-differential
    value, used in the localization of Federer 4.1.4, p. 348,
    with the derivative convention of 4.1.1, p. 346. *)
Theorem distribution_test_directional_derivative_value f x:U x ->
  smooth_test_value hE (DP f) x=
    @ContinuousMultilinear.evaluation R 1%N X Y NX NY hNX hNY [ffun _:'I_1=>v]
      (@D 1%N x (smooth_test_inclusion hE f)).
Proof.
move=>hx.
change (ev (smooth_test_inclusion hE (TOp f)) x=
  @ContinuousMultilinear.evaluation R 1%N X Y NX NY hNX hNY [ffun _: 'I_1=>v]
    (@D 1%N x (smooth_test_inclusion hE f))).
by rewrite test_directional_evaluation (@hP (smooth_test_inclusion hE f) x hx).
Qed.

(** Source for [distribution_test_directional_derivative_compact_support]:
    the actual test derivative retains each original compact
    support bound, used to localize derivatives in Federer
    4.1.4, p. 348, by 4.1.1, p. 346. *)
Theorem distribution_test_directional_derivative_compact_support
    (K:smooth_compact_set hNX U) f:
  support f `<=` smooth_compact_carrier K ->
  support (DP f) `<=` smooth_compact_carrier K.
Proof.
move=>hSupport.
change (@smooth_function_support R X Y NX hNX U E ev
  (smooth_test_inclusion hE (TOp f)) `<=` smooth_compact_carrier K).
rewrite test_directional_evaluation.
exact:(@smooth_directional_derivative_preserves_compact_support R X Y NX NY hNX hNY U hU
  E ev hE D hD v P hP K (smooth_test_inclusion hE f) hSupport).
Qed.

(** Source for [distribution_test_directional_derivative_support]:
    spt D_v f is contained in spt f, the original locality
    needed in Federer 4.1.4, p. 348. Actual compactness of
    spt f supplies the preceding compact-bound theorem. *)
Theorem distribution_test_directional_derivative_support f:
  support (DP f) `<=` support f.
Proof.
pose K:=@Build_smooth_compact_set R X NX hNX U (support f)
  (fun x hx=>hx.1) (smooth_test_support_compact hE f).
exact:(@distribution_test_directional_derivative_compact_support K f (fun _ hx=>hx)).
Qed.
End TestDirectionalValues.
