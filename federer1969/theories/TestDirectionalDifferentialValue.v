(** Federer (1969), 4.1.8, p. 360: actual test
    differentiation evaluates any actual first differential on the
    direction. This supporting adapter identifies the original test
    operators of 4.1.1, p. 346, with the differential
    convention already proved in 3.1.11, p. 219. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialDirectional
  ContinuousMultilinearSealed ContinuousMultilinearOne NormHigherDifferentialFirst
  SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothTestSpaces SmoothTestEvaluation
  DistributionDirectionalDerivative TestDirectionalValues.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section TestDirectionalDifferentialValue.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Variable E:lmodType R.
Variable ev:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY U ev.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Local Notation ez := (fun k=>@ContinuousMultilinear.evaluation R k X Y NX NY hNX hNY).
Local Notation ZN := (fun k=>@ContinuousMultilinear.norm R k X Y NX NY hNX hNY).
Local Notation hZ := (fun k=>@ContinuousMultilinear.laws R k X Y NX NY hNX hNY).
Variable D:forall k,X->Hom E (Z k).
Hypothesis hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D.
Local Notation DT := (smooth_test_space hE).
Local Notation Diff := (fun v=>@distribution_test_directional_derivative R X Y NX NY hNX hNY
  U hU E ev hE D hD v).

(** Source for [test_directional_derivative_actual_differential]:
    the original D_v phi equals Dphi(x)(v) for every
    actual differential Dphi(x), supporting the derivative passage
    through the first current in Federer 4.1.8, p. 360.
    No derivative or topology on a test-function space is assumed. *)
Theorem test_directional_derivative_actual_differential (f:DT) x (L:Hom X Y):
  U x->has_norm_differential NX NY U (smooth_test_value hE f) x L->
  forall v,smooth_test_value hE (Diff v f) x=L v.
Proof.
move=>hx hL v.
have hHigher:=@smooth_derivative_exact R X Y NX NY hNX hNY U E ev D hD
  1%N (smooth_test_inclusion hE f) x hx.
have hFirst:=(@norm_higher_differential_first R X Y NX NY hNX hNY Z ez ZN hZ
  U (ev (smooth_test_inclusion hE f)) x (@D 1%N x (smooth_test_inclusion hE f))).1 hHigher.
have hSame:=norm_differential_unique hNX hNY hL hFirst.
have hValue:=@distribution_test_directional_derivative_value R X Y NX NY hNX hNY U hU
  E ev hE D hD v f x hx.
exact:(eq_trans hValue (esym (congr1 (fun P:Hom X Y=>P v) hSame))).
Qed.
End TestDirectionalDifferentialValue.
