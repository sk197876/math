(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(6), p. 329:
    actual pointed pullback preserves the original
    germ value at the corresponding centre. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed HolomorphicAtUP HolomorphicGermArithmeticRepresentatives HolomorphicGermOperationsUP RealNormUP HolomorphicGermRepresentatives HolomorphicGermUP HolomorphicGermRingLaws HolomorphicGermRing
  HolomorphicGermValueUP HolomorphicGermValueSealed PointedHolomorphicPullbackUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [pointed_holomorphic_pullback_centre_value]:
    coordinate pullback at zero preserves the zero
    centre value used to choose the positive
    derivative order, 3.4.8(6), p. 329. *)
Theorem pointed_holomorphic_pullback_centre_value (R:realType) (X Y:lmodType (ComplexScalars.C R))
  (NX:X->R) (NY:Y->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (hNY:@is_real_norm R (restricted_space (ComplexScalars.embed R) Y) NY)
  (a:X) (b:Y) (u:X->Y)
  (P:holomorphic_germ_space hNY b->holomorphic_germ_space hNX a):
  is_pointed_holomorphic_germ_pullback u P ->u a = b ->forall beta,
    @HolomorphicGermValue.map R X NX hNX a (P beta) = @HolomorphicGermValue.map R Y NY hNY b beta.
Proof.
move=>hP hCentre beta.
have [f <-]:=@holomorphic_germ_has_representative R Y NY hNY b beta.
have [g [hG hValues]]:=hP f.
by rewrite hG (@HolomorphicGermValue.laws R X NX hNX a g)
  (@HolomorphicGermValue.laws R Y NY hNY b f) hValues hCentre.
Qed.
