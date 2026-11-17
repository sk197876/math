(** Supporting interface connection for Federer (1969),
    3.4.8(8), p. 329: the established
    analytic pullback satisfies the pointed
    all-representative specification at its actual
    target centre. No construction is replaced. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP NormAnalyticUP AnalyticGermUP AnalyticPullbackUP
  AnalyticPullbackRepresentative AnalyticPullbackSealed AnalyticPullbackRingMorphism PointedAnalyticPullbackUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [ordinary_analytic_pullback_pointed_laws]: the
    actual representative equation of 3.4.5,
    p. 319, gives the pointed specification
    used for the coordinate tower in
    3.4.8(8), p. 329. *)
Theorem ordinary_analytic_pullback_pointed_laws (R:realType) (X Y:lmodType R)
  (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
  (A:set X) (u:X->Y) (a:X)
  (hu:@norm_analytic_at R X Y NX NY hNX hNY A u a)
  (P:analytic_germ_space hNY (u a)->analytic_germ_space hNX a):
  is_analytic_germ_pullback hu P ->is_pointed_analytic_germ_pullback u P.
Proof.
move=>hP f.
exists (@analytic_pullback_representative R X Y NX NY hNX hNY A u a hu f).
split;first exact:hP f.
by move=>x.
Qed.

(** Source for [ordinary_analytic_ring_pullback_pointed_laws]:
    the existing ring pullback retains the
    same actual representative equation, supporting
    the original transverse coefficients in
    3.4.8(8), p. 329. *)
Theorem ordinary_analytic_ring_pullback_pointed_laws (R:realType) (X Y:lmodType R)
  (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
  (A:set X) (u:X->Y) (a:X)
  (hu:@norm_analytic_at R X Y NX NY hNX hNY A u a):
  is_pointed_analytic_germ_pullback u
    (@analytic_germ_ring_pullback R X Y NX NY hNX hNY A u a hu).
Proof.
apply:(@ordinary_analytic_pullback_pointed_laws R X Y NX NY hNX hNY A u a hu).
exact:(@AnalyticPullback.laws R X Y NX NY hNX hNY A u a hu).
Qed.
