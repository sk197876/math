(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(1),(8), pp. 326, 329:
    the original scalar constants form the
    distinguished copy of R in the holomorphic
    germ ring. State its representative law
    before selecting any ring homomorphism. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP RealNormUP HolomorphicGermUP HolomorphicGermRepresentatives HolomorphicGermArithmeticRepresentatives HolomorphicGermRing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_holomorphic_scalar_map]: the original
    identification Q_0=R in 3.4.8(1), p. 326,
    used in the quotient extension of (8),
    p. 329. Every original scalar maps
    to its actual constant-function germ. *)
Definition is_holomorphic_scalar_map (R:realType) (X:lmodType (ComplexScalars.C R))
  (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) a
  (scalar:{rmorphism (ComplexScalars.C R)->@holomorphic_germ_ring R X NX hNX a}):Prop:=
  forall c:ComplexScalars.C R,scalar c = holomorphic_germ (@holomorphic_constant_representative R X NX hNX a c).
