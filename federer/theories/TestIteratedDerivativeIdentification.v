(** Federer (1969), 4.1.1, p. 346: the
    iterated test operators are the original smooth
    partial derivatives, not hypothetical dual actions.
    Their values satisfy the recursive graph
    already proved in 3.1.11, p. 223. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom TensorUP RealNormUP NormDifferentialUP ContinuousMultilinearSealed
  NormIteratedDirectionalUP SmoothFunctionSpaceUP SmoothFunctionDerivativesUP
  SmoothDirectionalDerivativeSealed SmoothIteratedDirectional SmoothTestSpaces SmoothTestEvaluation
  TestDirectionalOperator DistributionDirectionalDerivative DistributionIteratedDerivative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section TestIteratedIdentification.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable U:X->Prop.
Hypothesis hU:forall x,U x ->norm_domain_interior NX U x.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.
Local Notation P := (fun v=>@SmoothDirectionalDerivative.operator R X Y NX NY hNX hNY U E ev hE D hD v).
Local Notation hP := (fun v=>@SmoothDirectionalDerivative.laws R X Y NX NY hNX hNY U E ev hE D hD v).
Local Notation inc := (smooth_test_inclusion hE).
Local Notation M := (@smooth_iterated_directional_operator R X E P).
Local Notation Q := (@distribution_test_iterated_derivative R X Y NX NY hNX hNY U hU E ev hE D hD).

(** Source for [test_iterated_derivative_inclusion]: repeated
    differentiation commutes with the inclusion into
    the actual smooth-function space, supporting
    Federer 4.1.1, p. 346. *)
Theorem test_iterated_derivative_inclusion s f:
  inc (Q s f)=M s (inc f).
Proof.
elim:s=>[|v s ih]; first reflexivity.
change (inc (@test_directional_operator R X Y NX NY hNX hNY U hU E ev hE D hD v (P v) (hP v)
  (Q s f))= P v (M s (inc f))).
by rewrite (@test_directional_evaluation R X Y NX NY hNX hNY U hU E ev hE D hD v (P v) (hP v)) ih.
Qed.

(** Source for [test_iterated_derivative_graph]: the actual
    test values satisfy the original iterated
    directional derivative graph, supporting TD^alpha
    in Federer 4.1.1, p. 346. *)
Theorem test_iterated_derivative_graph s f x:
  U x ->has_norm_iterated_directional NY U (smooth_test_value hE f) s x
    (smooth_test_value hE (Q s f) x).
Proof.
move=>hx.
have h:=@smooth_iterated_directional_graph R X Y NX NY hNX hNY U E ev D hD P hP s (inc f) x hx.
rewrite -test_iterated_derivative_inclusion in h; exact h.
Qed.
End TestIteratedIdentification.
