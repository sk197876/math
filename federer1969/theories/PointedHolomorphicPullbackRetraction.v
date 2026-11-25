(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(1),(5), pp. 326, 328:
    an actual coordinate section induces the inverse
    retraction equation on germs. Every representative is
    retained; no ring-image or closedness conclusion is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed HolomorphicAtUP HolomorphicGermArithmeticRepresentatives HolomorphicGermOperationsUP RealNormUP HolomorphicGermRepresentatives HolomorphicGermUP
  HolomorphicGermRingLaws PointedHolomorphicPullbackUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [pointed_holomorphic_germ_pullback_retraction]:
    actual coordinate projection and inclusion give the
    corresponding retraction of germ spaces, supporting
    the original coordinate subring in 3.4.8(1),(5), pp. 326, 328. *)
Theorem pointed_holomorphic_germ_pullback_retraction (R:realType) (X Y:lmodType (ComplexScalars.C R))
    (NX:X->R) (NY:Y->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (hNY:@is_real_norm R (restricted_space (ComplexScalars.embed R) Y) NY)
    (a:X) (b:Y) (u:X->Y) (v:Y->X)
    (P:holomorphic_germ_space hNY b->holomorphic_germ_space hNX a)
    (Q:holomorphic_germ_space hNX a->holomorphic_germ_space hNY b):
  is_pointed_holomorphic_germ_pullback u P ->is_pointed_holomorphic_germ_pullback v Q ->
  (forall y,u (v y)=y) ->forall alpha,Q (P alpha)=alpha.
Proof.
move=>hP hQ hSection alpha.
have [f <-]:=@holomorphic_germ_has_representative R Y NY hNY b alpha.
have [g [hG hValuesG]]:=hP f.
rewrite hG.
have [h [hH hValuesH]]:=hQ g.
rewrite hH;apply:holomorphic_germ_pointwise_equality=>y.
by rewrite hValuesH hValuesG hSection.
Qed.
