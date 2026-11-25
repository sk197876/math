(** Federer (1969), 3.4.7, p. 325: coefficient
    extension selected from proved existence and hidden
    behind its independent coefficient equation. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
From Federer Require Import CommutativePolynomialUP PolynomialCoefficientMapUP PolynomialCoefficientMapExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type PolynomialCoefficientMapSignature.
(** Source for [map]: the polynomial homomorphism induced
    by original coefficient extension, supporting 3.4.7, p. 325. *)
Parameter map:forall (A B C D:comNzRingType)
  (embedA:{rmorphism A->B}) (variableA:B) (source:B->nat->A)
  (embedC:{rmorphism C->D}) (variableC:D) (target:D->nat->C),
  is_commutative_polynomial_ring embedA variableA source ->
  is_commutative_polynomial_ring embedC variableC target ->
  {rmorphism A->C}->{rmorphism B->D}.
(** Source for [laws]: the coefficient equation specifying
    the extension in 3.4.7, p. 325. *)
Parameter laws:forall (A B C D:comNzRingType)
  (embedA:{rmorphism A->B}) (variableA:B) (source:B->nat->A)
  (embedC:{rmorphism C->D}) (variableC:D) (target:D->nat->C)
  (hSource:is_commutative_polynomial_ring embedA variableA source)
  (hTarget:is_commutative_polynomial_ring embedC variableC target) (phi:{rmorphism A->C}),
  is_polynomial_coefficient_map source target phi
    (@map A B C D embedA variableA source embedC variableC target hSource hTarget phi).
End PolynomialCoefficientMapSignature.
Module PolynomialCoefficientMap:PolynomialCoefficientMapSignature.
(** Source for [map]: a private choice from the
    proved homomorphism existence supporting 3.4.7, p. 325. *)
Definition map (A B C D:comNzRingType)
  (embedA:{rmorphism A->B}) (variableA:B) (source:B->nat->A)
  (embedC:{rmorphism C->D}) (variableC:D) (target:D->nat->C)
  (hSource:is_commutative_polynomial_ring embedA variableA source)
  (hTarget:is_commutative_polynomial_ring embedC variableC target) (phi:{rmorphism A->C}):
    {rmorphism B->D}:=
  projT1 (cid (@polynomial_coefficient_map_exists A B C D embedA variableA source
    embedC variableC target hSource hTarget phi)).
(** Source for [laws]: the selected map satisfies the
    independent original equation, supporting 3.4.7, p. 325. *)
Lemma laws (A B C D:comNzRingType)
  (embedA:{rmorphism A->B}) (variableA:B) (source:B->nat->A)
  (embedC:{rmorphism C->D}) (variableC:D) (target:D->nat->C)
  (hSource:is_commutative_polynomial_ring embedA variableA source)
  (hTarget:is_commutative_polynomial_ring embedC variableC target) (phi:{rmorphism A->C}):
  is_polynomial_coefficient_map source target phi
    (@map A B C D embedA variableA source embedC variableC target hSource hTarget phi).
Proof.
exact:(projT2 (cid (@polynomial_coefficient_map_exists A B C D embedA variableA source
  embedC variableC target hSource hTarget phi))).
Qed.
End PolynomialCoefficientMap.
