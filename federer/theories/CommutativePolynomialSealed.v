(** Federer (1969), 3.4.7, p. 325: the polynomial
    extension behind its independent coefficient laws. The
    finite-coefficient representation is private to existence. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
From Federer Require Import CommutativePolynomialUP FiniteCoefficientExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type CommutativePolynomialSignature.
(** Source for [space]: the polynomial algebra over
    the original coefficients, supporting 3.4.7, p. 325. *)
Parameter space:comNzRingType->comNzRingType.
(** Source for [embed]: original constant coefficients,
    supporting 3.4.7, p. 325. *)
Parameter embed:forall A:comNzRingType,{rmorphism A->space A}.
(** Source for [variable]: the independent polynomial
    variable, supporting 3.4.7, p. 325. *)
Parameter variable:forall A:comNzRingType,space A.
(** Source for [coefficient]: the unique finite coefficients,
    supporting 3.4.7, p. 325. *)
Parameter coefficient:forall A:comNzRingType,space A->nat->A.
(** Source for [laws]: the proved independent coefficient
    laws for the extension in 3.4.7, p. 325. *)
Parameter laws:forall A:comNzRingType,
  is_commutative_polynomial_ring (@embed A) (@variable A) (@coefficient A).
End CommutativePolynomialSignature.
Module CommutativePolynomial:CommutativePolynomialSignature.
(** Source for [space]: a hidden carrier selected from
    the existence proof supporting 3.4.7, p. 325. *)
Definition space (A:comNzRingType):comNzRingType:=
  projT1 (cid (commutative_polynomial_ring_exists A)).
(** Source for [embed]: the constant embedding from the
    same existence proof, supporting 3.4.7, p. 325. *)
Definition embed (A:comNzRingType):{rmorphism A->space A}:=
  projT1 (cid (projT2 (cid (commutative_polynomial_ring_exists A)))).
(** Source for [variable]: the variable from the same
    existence proof, supporting 3.4.7, p. 325. *)
Definition variable (A:comNzRingType):space A:=
  projT1 (cid (projT2 (cid (projT2 (cid (commutative_polynomial_ring_exists A)))))).
(** Source for [coefficient]: coefficients from the same
    existence proof, supporting 3.4.7, p. 325. *)
Definition coefficient (A:comNzRingType):space A->nat->A:=
  projT1 (cid (projT2 (cid (projT2 (cid (projT2 (cid (commutative_polynomial_ring_exists A)))))))).
(** Source for [laws]: the hidden witness satisfies the
    independent specification of 3.4.7, p. 325. *)
Lemma laws (A:comNzRingType):
  is_commutative_polynomial_ring (@embed A) (@variable A) (@coefficient A).
Proof.
exact:(projT2 (cid (projT2 (cid (projT2 (cid (projT2 (cid (commutative_polynomial_ring_exists A))))))))).
Qed.
End CommutativePolynomial.
