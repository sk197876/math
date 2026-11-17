(** Federer (1969), 3.4.8(1),(5), pp. 326, 328:
    the original representative laws determine each pointed
    coordinate pullback uniquely, independently of its selection. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP AnalyticGermRepresentatives AnalyticGermUP
  AnalyticGermRingLaws PointedAnalyticPullbackUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [pointed_analytic_germ_pullback_unique]: maps
    satisfying all original representative equations agree,
    supporting the opaque coordinate pullback in
    3.4.8(1),(5), pp. 326, 328. *)
Theorem pointed_analytic_germ_pullback_unique (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (a:X) (b:Y) (u:X->Y)
    (P Q:analytic_germ_space hNY b->analytic_germ_space hNX a):
  is_pointed_analytic_germ_pullback u P ->is_pointed_analytic_germ_pullback u Q ->
  forall alpha,P alpha=Q alpha.
Proof.
move=>hP hQ alpha.
have [f <-]:=@analytic_germ_has_representative R Y NY hNY b alpha.
have [g [hG hValuesG]]:=hP f.
have [h [hH hValuesH]]:=hQ f.
rewrite hG hH;apply:analytic_germ_pointwise_equality=>x.
by rewrite hValuesG hValuesH.
Qed.
