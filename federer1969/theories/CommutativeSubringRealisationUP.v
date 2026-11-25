(** Supporting algebra for Federer (1969), 3.4.8(5),
    p. 328: an abstract subring has a ring carrier
    with injective inclusion and exactly the prescribed image.
    This interface supports the Rees ring in Bourbaki,
    Commutative Algebra (1972), Chapter III, section 3,
    no. 1, Lemma 1, p. 197. *)
From mathcomp Require Import all_boot all_order ssralg boolp classical_sets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_commutative_subring_realisation]: the
    ring structure and exact inclusion of a specified
    subring, supporting the Rees ring in Bourbaki (1972),
    Chapter III, section 3, no. 1, Lemma 1, p. 197,
    for the expanded algebra of 3.4.8(5), p. 328. *)
Record is_commutative_subring_realisation (A:comNzRingType) (S:set A)
    (C:comNzRingType) (inclusion:{rmorphism C->A}):Prop:={
  (** Source for [commutative_subring_inclusion_injective]:
      the ring inclusion is injective, supporting the
      subring construction in the cited Lemma 1. *)
  commutative_subring_inclusion_injective:injective inclusion;
  (** Source for [commutative_subring_inclusion_image]:
      the image is precisely the original subring,
      supporting the cited Lemma 1. *)
  commutative_subring_inclusion_image:forall a:A,S a <->exists c:C,inclusion c=a
}.
