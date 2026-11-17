(** Federer (1969), 3.4.12, p. 339, extending
    3.4.8(8), p. 329: equal original
    centres have inverse germ-ring identifications
    with the identity representative equation.
    Equality elimination proves existence. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed RealNormUP HolomorphicGermUP HolomorphicGermRing PointedHolomorphicPullbackUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [equal_holomorphic_germ_centres_ring_witnesses]:
    identify the original coefficient centre P(0)
    with zero, proved equal by linearity,
    in 3.4.8(8), p. 329. Both
    maps preserve every original representative;
    neither implementation is exposed. *)
Theorem equal_holomorphic_germ_centres_ring_witnesses (R:realType) (X:lmodType (ComplexScalars.C R))
  (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) (a b:X):
  a = b ->exists
    (F:{rmorphism [the comNzRingType of (@holomorphic_germ_ring R X NX hNX a)]->
      [the comNzRingType of (@holomorphic_germ_ring R X NX hNX b)]})
    (G:{rmorphism [the comNzRingType of (@holomorphic_germ_ring R X NX hNX b)]->
      [the comNzRingType of (@holomorphic_germ_ring R X NX hNX a)]}),
    is_pointed_holomorphic_germ_pullback idfun F /\is_pointed_holomorphic_germ_pullback idfun G /\
    cancel F G /\cancel G F.
Proof.
move=> <-.
pose identity:{rmorphism [the comNzRingType of (@holomorphic_germ_ring R X NX hNX a)]->
    [the comNzRingType of (@holomorphic_germ_ring R X NX hNX a)]}:=
  GRing.RMorphism.clone _ _ idfun _.
have hIdentity:is_pointed_holomorphic_germ_pullback idfun identity.
  move=>f;exists f;by split.
exists identity,identity;by split;last split;last split.
Qed.
