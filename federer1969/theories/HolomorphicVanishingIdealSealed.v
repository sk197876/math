(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(5), p. 328:
    the original vanishing ideal behind its opaque
    centre-value interface. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP ComplexModulus ComplexScalarNorm RealNormUP HolomorphicGermRing HolomorphicVanishingIdealUP HolomorphicVanishingIdealExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type HolomorphicVanishingIdealSignature.
(** Source for [value]: the local vanishing ideal
    used in 3.4.7, p. 325, and 3.4.8(5), p. 328. *)
Parameter value:forall (R:realType) (X:lmodType (ComplexScalars.C R)) (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) a,
  set (@holomorphic_germ_ring R X NX hNX a).
(** Source for [laws]: the original centre-value membership
    laws, supporting the same arguments, pp. 325, 328. *)
Parameter laws:forall (R:realType) (X:lmodType (ComplexScalars.C R)) (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) a,
  is_holomorphic_vanishing_ideal (@value R X NX hNX a).
End HolomorphicVanishingIdealSignature.
Module HolomorphicVanishingIdeal:HolomorphicVanishingIdealSignature.
(** Source for [value]: private choice from proved
    existence, supporting 3.4.8(5), p. 328. *)
Definition value (R:realType) (X:lmodType (ComplexScalars.C R)) (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) a:=
  projT1 (cid (@holomorphic_vanishing_ideal_exists R X NX hNX a)).
(** Source for [laws]: the hidden ideal satisfies
    the independent laws, supporting 3.4.8(5), p. 328. *)
Lemma laws (R:realType) (X:lmodType (ComplexScalars.C R)) (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX) a:
  is_holomorphic_vanishing_ideal (@value R X NX hNX a).
Proof. exact:(projT2 (cid (@holomorphic_vanishing_ideal_exists R X NX hNX a))). Qed.
End HolomorphicVanishingIdeal.
