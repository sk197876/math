(** Federer (1969), 3.4.8(8), p. 329:
    the original quotient ring and canonical map
    behind independent opaque kernel and surjection
    laws. The quotient implementation stays private. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeIdealUP CommutativeQuotientUP CommutativeQuotientExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type CommutativeIdealQuotientSignature.
(** Source for [space]: the original proper-ideal
    quotient ring, 3.4.8(8), p. 329. *)
Parameter space:forall (K:fieldType) (A:comNzRingType) (scalar:{rmorphism K->A}) (I:set A),
  is_commutative_ideal I ->~I 1 ->comNzRingType.
(** Source for [projection]: the original canonical
    ring homomorphism p, 3.4.8(8), p. 329. *)
Parameter projection:forall (K:fieldType) (A:comNzRingType) (scalar:{rmorphism K->A}) (I:set A)
  (hI:is_commutative_ideal I) (hProper:~I 1),{rmorphism A->@space K A scalar I hI hProper}.
(** Source for [laws]: the original surjection and
    exact kernel equations, 3.4.8(8), p. 329. *)
Parameter laws:forall (K:fieldType) (A:comNzRingType) (scalar:{rmorphism K->A}) (I:set A)
  (hI:is_commutative_ideal I) (hProper:~I 1),
  is_commutative_ideal_quotient I (@projection K A scalar I hI hProper).
End CommutativeIdealQuotientSignature.
Module CommutativeIdealQuotient:CommutativeIdealQuotientSignature.
(** Source for [space]: private selection from the
    proved original quotient existence theorem,
    3.4.8(8), p. 329. *)
Definition space (K:fieldType) (A:comNzRingType) (scalar:{rmorphism K->A}) (I:set A)
  (hI:is_commutative_ideal I) (hProper:~I 1):comNzRingType:=
  projT1 (cid (@scalar_commutative_quotient_exists K A scalar I hI hProper)).
(** Source for [projection]: the private original
    canonical projection, 3.4.8(8), p. 329. *)
Definition projection (K:fieldType) (A:comNzRingType) (scalar:{rmorphism K->A}) (I:set A)
  (hI:is_commutative_ideal I) (hProper:~I 1):{rmorphism A->@space K A scalar I hI hProper}:=
  projT1 (cid (projT2 (cid (@scalar_commutative_quotient_exists K A scalar I hI hProper)))).
(** Source for [laws]: the selected quotient satisfies
    the exact independent original laws,
    3.4.8(8), p. 329. *)
Lemma laws (K:fieldType) (A:comNzRingType) (scalar:{rmorphism K->A}) (I:set A)
  (hI:is_commutative_ideal I) (hProper:~I 1):
  is_commutative_ideal_quotient I (@projection K A scalar I hI hProper).
Proof. exact:(projT2 (cid (projT2 (cid (@scalar_commutative_quotient_exists K A scalar I hI hProper))))). Qed.
End CommutativeIdealQuotient.
