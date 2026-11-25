(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(1),(5), pp. 326, 328:
    the original representative laws determine each pointed
    coordinate pullback uniquely, independently of its selection. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed HolomorphicAtUP HolomorphicGermArithmeticRepresentatives HolomorphicGermOperationsUP RealNormUP HolomorphicGermRepresentatives HolomorphicGermUP
  HolomorphicGermRingLaws PointedHolomorphicPullbackUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [pointed_holomorphic_germ_pullback_unique]: maps
    satisfying all original representative equations agree,
    supporting the opaque coordinate pullback in
    3.4.8(1),(5), pp. 326, 328. *)
Theorem pointed_holomorphic_germ_pullback_unique (R:realType) (X Y:lmodType (ComplexScalars.C R))
    (NX:X->R) (NY:Y->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (hNY:@is_real_norm R (restricted_space (ComplexScalars.embed R) Y) NY)
    (a:X) (b:Y) (u:X->Y)
    (P Q:holomorphic_germ_space hNY b->holomorphic_germ_space hNX a):
  is_pointed_holomorphic_germ_pullback u P ->is_pointed_holomorphic_germ_pullback u Q ->
  forall alpha,P alpha=Q alpha.
Proof.
move=>hP hQ alpha.
have [f <-]:=@holomorphic_germ_has_representative R Y NY hNY b alpha.
have [g [hG hValuesG]]:=hP f.
have [h [hH hValuesH]]:=hQ f.
rewrite hG hH;apply:holomorphic_germ_pointwise_equality=>x.
by rewrite hValuesG hValuesH.
Qed.
