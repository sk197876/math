(** Federer (1969), 3.4.12, p. 339, extending 3.4.5, p. 319: the map on
    original analytic germs is specified by all representative
    equations before its existence or selection. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexModulus ComplexScalarNorm HolomorphicGermArithmeticRepresentatives RealNormUP HolomorphicAtUP HolomorphicGermRepresentatives
  HolomorphicGermUP HolomorphicPullbackRepresentative.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_holomorphic_germ_pullback]: the displayed
    representative equation for the induced map in 3.4.5,
    p. 319, required for every original analytic representative. *)
Definition is_holomorphic_germ_pullback (R:realType) (X Y:lmodType (ComplexScalars.C R))
    (NX:X->R) (NY:Y->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (hNY:@is_real_norm R (restricted_space (ComplexScalars.embed R) Y) NY)
    (A:set X) (u:X->Y) (a:X)
    (hu:@is_holomorphic_at R X Y NX NY hNX hNY A u a)
    (P:holomorphic_germ_space hNY (u a)->holomorphic_germ_space hNX a):Prop:=
  forall f:@holomorphic_representative_type R Y NY hNY (u a),
    P (holomorphic_germ f)=holomorphic_germ (@holomorphic_pullback_representative R X Y NX NY hNX hNY A u a hu f).
