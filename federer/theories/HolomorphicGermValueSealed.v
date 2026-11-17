(** Federer (1969), 3.4.12, p. 339, extending 3.4.7, p. 325: original germ
    values behind their proved representative equation. No
    representative choice is exposed to downstream proofs. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed HolomorphicGermArithmeticRepresentatives HolomorphicGermOperationsUP RealNormUP HolomorphicGermUP HolomorphicGermRing HolomorphicGermValueUP HolomorphicGermValueExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type HolomorphicGermValueSignature.
(** Source for [map]: the original value at the
    centre as a ring homomorphism, supporting 3.4.7, p. 325. *)
Parameter map:forall (R:realType) (X:lmodType (ComplexScalars.C R)) (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) a,
  {rmorphism [the comNzRingType of (@holomorphic_germ_ring R X NX hNX a)]->(ComplexScalars.C R)}.
(** Source for [laws]: every original representative gives
    this value, supporting 3.4.7, p. 325. *)
Parameter laws:forall (R:realType) (X:lmodType (ComplexScalars.C R)) (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) a,
  is_holomorphic_germ_value_at_centre (@map R X NX hNX a).
End HolomorphicGermValueSignature.
Module HolomorphicGermValue:HolomorphicGermValueSignature.
(** Source for [map]: a hidden choice from proved
    centre-value existence, supporting 3.4.7, p. 325. *)
Definition map (R:realType) (X:lmodType (ComplexScalars.C R)) (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) a:
    {rmorphism [the comNzRingType of (@holomorphic_germ_ring R X NX hNX a)]->(ComplexScalars.C R)}:=
  projT1 (cid (@holomorphic_germ_value_exists R X NX hNX a)).
(** Source for [laws]: the hidden homomorphism satisfies
    the independent original representative equation,
    supporting 3.4.7, p. 325. *)
Lemma laws (R:realType) (X:lmodType (ComplexScalars.C R)) (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) a:
  is_holomorphic_germ_value_at_centre (@map R X NX hNX a).
Proof. exact:(projT2 (cid (@holomorphic_germ_value_exists R X NX hNX a))). Qed.
End HolomorphicGermValue.
