(** Federer (1969), 4.1.27, p. 384:
    the coordinate partial derivatives of a
    multiaffine map are identified by its exact
    coordinate-line increments. Reuse the directional
    quotient and uniqueness laws of 3.1.1,
    p. 209; no approximation to the
    actual differential is substituted. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  NormDifferentialDirectional NormedCurveDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_differential_exact_line_increment]: the exact
    coordinate-line calculation used for D_i f
    in 4.1.27, p. 384. This is
    a supporting application of the original
    directional quotient in 3.1.1, p. 209. *)
Theorem norm_differential_exact_line_increment (R:realType)
    (X Y:lmodType R) (NX:X->R) (NY:Y->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:set X) (f:X->Y) a (L:Hom X Y) (v:X) (w:Y):
  has_norm_differential NX NY A f a L->
  (forall t:R,f (a+t*:v)-f a=t*:w)->L v=w.
Proof.
move=>hD hIncrement.
apply:(@punctured_norm_limit_unique R Y NY hNY
  (fun t:R=>t^-1*:(f (a+t*:v)-f a)) (L v) w).
- exact:(@norm_differential_directional_limit R X Y NX NY hNX hNY A f a L hD v).
- move=>epsilon hEpsilon;exists 1;split;first exact:ltr01.
  move=>t /andP[hT _].
  have hNonzero:t!=0 by move:hT;rewrite normr_gt0.
  by rewrite hIncrement scalerA mulVf // scale1r subrr (real_seminorm_zero hNY.1).
Qed.
