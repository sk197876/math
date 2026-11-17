(** Federer (1969), 3.4.7, p. 325: the coefficient
    fraction field behind its independently specified embedding
    and representation laws. Quotient pairs remain private. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
From Federer Require Import CommutativeDomainUP FractionFieldUP FractionFieldExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type FractionFieldSignature.
(** Source for [space]: a field of fractions for
    the original domain, supporting 3.4.7, p. 325. *)
Parameter space:forall A:comNzRingType,is_commutative_integral_domain A->fieldType.
(** Source for [embed]: the faithful coefficient embedding,
    supporting the Gauss argument in 3.4.7, p. 325. *)
Parameter embed:forall (A:comNzRingType) (hDomain:is_commutative_integral_domain A),
  {rmorphism A->space hDomain}.
(** Source for [laws]: the independent fraction-field
    laws supporting 3.4.7, p. 325. *)
Parameter laws:forall (A:comNzRingType) (hDomain:is_commutative_integral_domain A),
  is_commutative_fraction_field (@embed A hDomain).
End FractionFieldSignature.
Module FractionField:FractionFieldSignature.
(** Source for [space]: the hidden field selected from
    proved existence, supporting 3.4.7, p. 325. *)
Definition space (A:comNzRingType) (hDomain:is_commutative_integral_domain A):fieldType:=
  projT1 (cid (commutative_fraction_field_exists hDomain)).
(** Source for [embed]: the embedding from the same
    existence witness, supporting 3.4.7, p. 325. *)
Definition embed (A:comNzRingType) (hDomain:is_commutative_integral_domain A):
    {rmorphism A->space hDomain}:=
  projT1 (cid (projT2 (cid (commutative_fraction_field_exists hDomain)))).
(** Source for [laws]: the hidden field satisfies the
    independent original laws, supporting 3.4.7, p. 325. *)
Lemma laws (A:comNzRingType) (hDomain:is_commutative_integral_domain A):
  is_commutative_fraction_field (@embed A hDomain).
Proof. exact:(projT2 (cid (projT2 (cid (commutative_fraction_field_exists hDomain))))). Qed.
End FractionField.
