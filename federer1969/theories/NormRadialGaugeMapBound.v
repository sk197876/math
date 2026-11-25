(** Federer (1969), 3.2.35, p. 271:
    a proved pairwise norm estimate for the
    corrected radial boundary map on the unit sphere. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import RealNormUP PositiveReciprocalDifferenceBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_radial_gauge_pairwise_bound]:
    supporting Lipschitzness of the boundary
    parametrization in Federer 3.2.35, p. 271,
    corrected by erratum p. 5, book p. 271
    line 24. On the unit sphere, inverse
    bounds M and a scalar difference bound C
    give the explicit radial bound M+M^2*C.
    This supporting pointwise estimate precedes the
    discharge of its bounds from the original
    bounded open convex-body hypotheses. *)
Lemma norm_radial_gauge_pairwise_bound (R:realType) (V:lmodType R)
    (N:V->R) (hN:is_real_norm N) (g:V->R) x y M C:
  N x= 1 ->N y= 1 ->0<g x ->0<g y ->
  (g x)^-1<=M ->(g y)^-1<=M ->`|g x-g y|<=C*N (x-y) ->
  N ((g x)^-1*:x-(g y)^-1*:y)<=(M+M^+2*C)*N (x-y).
Proof.
move=>hX hY hGX hGY hInvX hInvY hScalar.
have hPositiveInverse:0<(g x)^-1 by rewrite invr_gt0.
have hSplit:(g x)^-1*:x-(g y)^-1*:y=
    (g x)^-1*:(x-y)+((g x)^-1-(g y)^-1)*:y.
  by rewrite scalerBr scalerBl addrA subrK.
have hTriangle:=real_seminorm_triangle hN.1
  ((g x)^-1*:(x-y)) (((g x)^-1-(g y)^-1)*:y).
rewrite -hSplit !(real_seminorm_scale hN.1) hY mulr1
  (ger0_norm (ltW hPositiveInverse)) in hTriangle.
have hFirst:(g x)^-1*N (x-y)<=M*N (x-y).
  exact:(ler_wpM2r (real_seminorm_nonnegative hN.1 (x-y)) hInvX).
have hReciprocal:=positive_reciprocal_difference_bound hGX hGY hInvX hInvY.
have hSecond:`|(g x)^-1-(g y)^-1|<=M^+2*(C*N (x-y)).
  exact:(le_trans hReciprocal (ler_wpM2l (sqr_ge0 M) hScalar)).
apply:(le_trans hTriangle _).
apply:(le_trans (lerD hFirst hSecond) _).
by rewrite mulrA -mulrDl.
Qed.
