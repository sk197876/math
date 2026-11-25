(** Federer (1969), 4.1.1, p. 346: evaluate the actual
    first differential in a fixed direction. Bounded linear
    postcomposition and the previous class-loss theorem give
    smoothness with no new calculus argument. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP ContinuousMultilinearUP
  ContinuousMultilinearSealed ContinuousMultilinearNorm NormRegularity NormRegularityLinearMaps
  SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothFirstDerivativeRegularity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Section DirectionalEvaluation.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Local Notation evZ := (fun k=>@ContinuousMultilinear.evaluation R k X Y NX NY hNX hNY).
Local Notation ZN := (fun k=>@ContinuousMultilinear.norm R k X Y NX NY hNX hNY).
Local Notation hZ := (fun k=>@ContinuousMultilinear.laws R k X Y NX NY hNX hNY).

(** Source for [first_derivative_directional_evaluation_bound]:
    the first derivative evaluated at v has norm at most
    ||v|| times its operator norm, supporting D_j phi in
    Federer 4.1.1, p. 346, by the original 3.1.11 norm. *)
Theorem first_derivative_directional_evaluation_bound (v:X):
  norm_bounded_linear (@ZN 1%N) NY (@evZ 1%N [ffun _: 'I_1=>v]).
Proof.
exists (NX v); split; first exact:real_seminorm_nonnegative hNX.1 v.
move=>z.
have hb:=multilinear_operator_bound (continuous_multilinear_norm_laws (hZ 1%N) z)
  [ffun _: 'I_1=>v].
by rewrite big_ord1 ffunE mulrC in hb.
Qed.

Variable U:set X.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.

(** Source for [smooth_directional_evaluation_regular]: the
    actual directional derivative of a smooth function is smooth,
    supporting the test-function operators of Federer 4.1.1,
    p. 346. All finite orders use the same derivative field. *)
Theorem smooth_directional_evaluation_regular f v:
  norm_class_all_orders hNX hNY U
    (fun x=>@evZ 1%N [ffun _: 'I_1=>v] (@D 1%N x f)).
Proof.
move=>k.
exact:(@norm_class_postcompose_linear R X (Z 1%N) Y NX (@ZN 1%N) NY hNX
  (continuous_multilinear_norm_is_norm hNY (hZ 1%N)) hNY U
  (fun x=>@D 1%N x f) (@evZ 1%N [ffun _: 'I_1=>v]) k
  (first_derivative_directional_evaluation_bound v)
  (smooth_first_derivative_field_regular hE hD f k)).
Qed.
End DirectionalEvaluation.
