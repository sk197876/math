(** Federer (1969), 4.1.1, p. 345: actual multiplication
    of tests by any smooth scalar. The product is the
    opaque E multiplier corestricted to D, with its
    original evaluation, support and continuity laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric NormDifferentialUP NormRegularity
  ContinuousMultilinearSealed CompactSupportFunctionUP OpenFamilyTopologyUP SmoothFunctionSpaceUP
  SmoothFunctionDerivativesUP SmoothFunctionSupport SmoothTestSpaces SmoothTestEvaluation SmoothTestTopology
  SmoothMultiplierUP SmoothMultiplierSealed SmoothMultiplierSupport TestMultiplierOperator.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section TestScalarMultiplier.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable U:set X.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Variable u:X->R.
Hypothesis hu:norm_class_all_orders hNX (@scalar_absolute_value_norm R) U u.
Local Notation DT := (smooth_test_space hE).
Local Notation value := (smooth_test_value hE).
Local Notation P := (@SmoothMultiplier.operator R X Y NX NY hNX hNY U E ev hE u hu).
Local Notation hP := (@SmoothMultiplier.laws R X Y NX NY hNX hNY U E ev hE u hu).

(** Source for [smooth_test_scalar_multiplier]: the actual
    test map phi to u phi, used in T L v_s of
    Federer 4.1.1, p. 345. *)
Definition smooth_test_scalar_multiplier:Hom DT DT:=
  @test_multiplier_operator R X Y NX NY hNX hNY U E ev hE u P hP.

(** Source for [smooth_test_scalar_multiplier_value]: exact
    pointwise multiplication on U, supporting Federer
    4.1.1, p. 345. *)
Lemma smooth_test_scalar_multiplier_value f x:U x ->
  value (smooth_test_scalar_multiplier f) x=u x*:value f x.
Proof.
move=>hx; rewrite /smooth_test_value /smooth_test_scalar_multiplier test_multiplier_evaluation.
exact:(hP (smooth_test_inclusion hE f) hx).
Qed.

(** Source for [smooth_test_scalar_multiplier_laws]: the
    actual test multiplier satisfies the independent
    evaluation specification, supporting Federer 4.1.1,
    p. 345. *)
Lemma smooth_test_scalar_multiplier_laws:
  is_smooth_multiplier U value u smooth_test_scalar_multiplier.
Proof. exact:smooth_test_scalar_multiplier_value. Qed.

(** Source for [smooth_test_scalar_multiplier_support]:
    the product support is contained in the actual scalar
    support, supporting the associated partition in
    Federer 4.1.1, p. 345. *)
Theorem smooth_test_scalar_multiplier_support f:
  @smooth_function_support R X Y NX hNX U DT value (smooth_test_scalar_multiplier f) `<=`
    @real_function_support R (real_norm_metric_space hNX) u.
Proof.
change (@smooth_function_support R X Y NX hNX U E ev
  (smooth_test_inclusion hE (smooth_test_scalar_multiplier f)) `<=`
    @real_function_support R (real_norm_metric_space hNX) u).
rewrite /smooth_test_scalar_multiplier test_multiplier_evaluation.
exact (@smooth_multiplier_scalar_support_subset R X Y NX NY hNX hNY U E ev hE u P hP
  (smooth_test_inclusion hE f)).
Qed.

Hypothesis hU:forall x,U x ->norm_domain_interior NX U x.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.

(** Source for [smooth_test_scalar_multiplier_continuous]:
    scalar multiplication by u is continuous on the
    literal final D topology, supporting T L v_s in
    Federer 4.1.1, p. 345. *)
Theorem smooth_test_scalar_multiplier_continuous:
  open_family_continuous (smooth_test_opens hE hD) (smooth_test_opens hE hD)
    smooth_test_scalar_multiplier.
Proof.
exact:(@test_multiplier_operator_continuous R X Y NX NY hNX hNY U hU E ev hE D hD u hu P hP).
Qed.
End TestScalarMultiplier.
