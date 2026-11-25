(** Federer (1969), 3.4.8(6), p. 329:
    the original coordinate subring is preserved by
    fixed-tail coordinate changes. Actual representative
    equations turn the coordinate square into an
    exact image-retraction equation on germs. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP AnalyticGermRepresentatives AnalyticGermUP
  AnalyticGermRingLaws PointedAnalyticPullbackUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [pointed_analytic_image_preservation]: the
    exact pullback-image equation supporting Q_j invariance
    under H_j, 3.4.8(6), p. 329. The coordinate
    square is an actual equality of maps; its
    original analytic instances are proved separately. *)
Theorem pointed_analytic_image_preservation (R:realType) (X Y:lmodType R)
  (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
  (a:X) (b:Y) (u:X->Y) (v:Y->X) (h:X->X)
  (P:analytic_germ_space hNY b->analytic_germ_space hNX a)
  (S:analytic_germ_space hNX a->analytic_germ_space hNY b)
  (H:analytic_germ_space hNX a->analytic_germ_space hNX a):
  is_pointed_analytic_germ_pullback u P ->is_pointed_analytic_germ_pullback v S ->
  is_pointed_analytic_germ_pullback h H ->
  (forall x,u (h (v (u x))) = u (h x)) ->
  forall beta,P (S (H (P beta))) = H (P beta).
Proof.
move=>hP hS hH hSquare beta.
have [f <-]:=@analytic_germ_has_representative R Y NY hNY b beta.
have [g [hG hValuesG]]:=hP f.
have [k [hK hValuesK]]:=hH g.
have [l [hL hValuesL]]:=hS k.
have [m [hM hValuesM]]:=hP l.
rewrite hG hK hL hM;apply:analytic_germ_pointwise_equality=>x.
by rewrite hValuesM hValuesL !hValuesK !hValuesG hSquare.
Qed.
