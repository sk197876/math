(** Federer (1969), 4.1.2, p. 347: the
    directional operator on the abstract smooth space
    evaluates every actual ordinary first differential.
    This connects the kernel translation calculus to
    the already proved test quotient estimates. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialDirectional
  ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearOne
  NormHigherDifferentialUP NormHigherDifferentialFirst SmoothFunctionDerivativesUP SmoothDirectionalDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [smooth_directional_ordinary_evaluation]: the actual
    directional derivative of a kernel test in Federer
    4.1.2, p. 347, is its original
    ordinary differential applied to the chosen direction. *)
Theorem smooth_directional_ordinary_evaluation (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U:set X) (E:lmodType R) (ev:E->X->Y)
    (D:forall j,X->Hom E (@ContinuousMultilinear.space R j X Y NX NY hNX hNY))
    (hD:@is_smooth_function_derivatives R X Y NX NY hNX hNY U E ev D)
    v (P:Hom E E):
  @is_smooth_directional_derivative R X Y NX NY hNX hNY U E ev D v P ->
  forall f x (L:Hom X Y),U x ->
    has_norm_differential NX NY U (ev f) x L ->ev (P f) x=L v.
Proof.
move=>hP f x L hx hL.
pose Z:=fun j=>@ContinuousMultilinear.space R j X Y NX NY hNX hNY.
pose ez:=fun j=>@ContinuousMultilinear.evaluation R j X Y NX NY hNX hNY.
pose ZN:=fun j=>@ContinuousMultilinear.norm R j X Y NX NY hNX hNY.
pose hZ:=fun j=>@ContinuousMultilinear.laws R j X Y NX NY hNX hNY.
have hHigher:=@smooth_derivative_exact R X Y NX NY hNX hNY U E ev D hD 1%N f x hx.
have hOrdinary:=(@norm_higher_differential_first R X Y NX NY hNX hNY Z ez ZN hZ U
  (ev f) x (@D 1%N x f)).1 hHigher.
have hEqual:=norm_differential_unique hNX hNY hOrdinary hL.
rewrite (@hP f x hx).
change ((continuous_multilinear_one_operator (hZ 1%N) (@D 1%N x f)) v=L v).
by rewrite hEqual.
Qed.
