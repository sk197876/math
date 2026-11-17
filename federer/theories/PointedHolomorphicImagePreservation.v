(** Federer (1969), 3.4.12, pp. 338–339: complex extension
    of the passages identified below. Earlier real and algebraic
    source locators are retained for the results reused here. *)
(** Federer (1969), 3.4.8(6), p. 329:
    the original coordinate subring is preserved by
    fixed-tail coordinate changes. Actual representative
    equations turn the coordinate square into an
    exact image-retraction equation on germs. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed RealNormUP HolomorphicGermRepresentatives HolomorphicGermUP
  HolomorphicGermRingLaws PointedHolomorphicPullbackUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [pointed_holomorphic_image_preservation]: the
    exact pullback-image equation supporting Q_j invariance
    under H_j, 3.4.8(6), p. 329. The coordinate
    square is an actual equality of maps; its
    original holomorphic instances are proved separately. *)
Theorem pointed_holomorphic_image_preservation (R:realType) (X Y:lmodType (ComplexScalars.C R))
  (NX:X->R) (NY:Y->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (hNY:@is_real_norm R (restricted_space (ComplexScalars.embed R) Y) NY)
  (a:X) (b:Y) (u:X->Y) (v:Y->X) (h:X->X)
  (P:holomorphic_germ_space hNY b->holomorphic_germ_space hNX a)
  (S:holomorphic_germ_space hNX a->holomorphic_germ_space hNY b)
  (H:holomorphic_germ_space hNX a->holomorphic_germ_space hNX a):
  is_pointed_holomorphic_germ_pullback u P ->is_pointed_holomorphic_germ_pullback v S ->
  is_pointed_holomorphic_germ_pullback h H ->
  (forall x,u (h (v (u x))) = u (h x)) ->
  forall beta,P (S (H (P beta))) = H (P beta).
Proof.
move=>hP hS hH hSquare beta.
have [f <-]:=@holomorphic_germ_has_representative R Y NY hNY b beta.
have [g [hG hValuesG]]:=hP f.
have [k [hK hValuesK]]:=hH g.
have [l [hL hValuesL]]:=hS k.
have [m [hM hValuesM]]:=hP l.
rewrite hG hK hL hM;apply:holomorphic_germ_pointwise_equality=>x.
by rewrite hValuesM hValuesL !hValuesK !hValuesG hSquare.
Qed.
