(** Federer (1969), 3.4.8(1),(5), pp. 326, 328:
    an actual coordinate section induces the inverse
    retraction equation on germs. Every representative is
    retained; no ring-image or closedness conclusion is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP AnalyticGermRepresentatives AnalyticGermUP
  AnalyticGermRingLaws PointedAnalyticPullbackUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [pointed_analytic_germ_pullback_retraction]:
    actual coordinate projection and inclusion give the
    corresponding retraction of germ spaces, supporting
    the original coordinate subring in 3.4.8(1),(5), pp. 326, 328. *)
Theorem pointed_analytic_germ_pullback_retraction (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (a:X) (b:Y) (u:X->Y) (v:Y->X)
    (P:analytic_germ_space hNY b->analytic_germ_space hNX a)
    (Q:analytic_germ_space hNX a->analytic_germ_space hNY b):
  is_pointed_analytic_germ_pullback u P ->is_pointed_analytic_germ_pullback v Q ->
  (forall y,u (v y)=y) ->forall alpha,Q (P alpha)=alpha.
Proof.
move=>hP hQ hSection alpha.
have [f <-]:=@analytic_germ_has_representative R Y NY hNY b alpha.
have [g [hG hValuesG]]:=hP f.
rewrite hG.
have [h [hH hValuesH]]:=hQ g.
rewrite hH;apply:analytic_germ_pointwise_equality=>y.
by rewrite hValuesH hValuesG hSection.
Qed.
