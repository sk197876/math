(** Federer (1969), 3.4.12, p. 339, extending 3.4.7, p. 325: values at
    the origin detect units and specialize the transverse
    coefficients. The value map is specified by every
    actual representative before its existence is proved. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed HolomorphicGermArithmeticRepresentatives HolomorphicGermOperationsUP RealNormUP HolomorphicGermRepresentatives HolomorphicGermUP HolomorphicGermRing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [is_holomorphic_germ_value_at_centre]: the
    original value at the centre is independent of
    the analytic representative, supporting units and coefficient
    specialization in 3.4.7, p. 325. *)
Definition is_holomorphic_germ_value_at_centre (R:realType) (X:lmodType (ComplexScalars.C R))
    (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) a
    (value:{rmorphism [the comNzRingType of (@holomorphic_germ_ring R X NX hNX a)]->(ComplexScalars.C R)}):Prop:=
  forall f:@holomorphic_representative_type R X NX hNX a,
    value (holomorphic_germ f) = holomorphic_representative_value f a.
