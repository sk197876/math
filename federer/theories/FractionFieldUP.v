(** Federer (1969), 3.4.7, p. 325: the
    Gauss argument compares the polynomial extension with
    its coefficient field of fractions. These independent
    laws precede the existence proof and expose no
    fraction-pair representation. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_commutative_fraction_field]: supporting
    field-of-fractions laws for the Gauss lemma invoked
    in 3.4.7, p. 325. Original coefficients
    embed injectively, and every field element is
    a fraction with an original nonzero denominator.
    No polynomial factorization law is assumed. *)
Record is_commutative_fraction_field (A:comNzRingType) (K:fieldType)
    (embed:{rmorphism A->K}):Prop:={
  (** Source for [fraction_field_embedding_injective]: the
      original coefficient ring embeds faithfully, supporting
      the Gauss argument in 3.4.7, p. 325. *)
  fraction_field_embedding_injective:injective embed;
  (** Source for [fraction_field_fraction_representation]:
      every fraction uses original coefficients and a
      nonzero denominator, supporting 3.4.7, p. 325. *)
  fraction_field_fraction_representation:forall x:K,exists a b:A,
    b<>0 /\x = embed a/(embed b)
}.
