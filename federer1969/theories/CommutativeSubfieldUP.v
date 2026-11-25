(** Federer (1969), 3.4.8(8), p. 329:
    the original coefficient subfield is closed under
    ring operations and inverses. State these laws
    before realising its field carrier. Source for
    the supporting adjunction: Bourbaki, Algebra II
    (1990), Chapter V, section 2, no. 3, pp. V.10–11. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeSubringUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_commutative_subfield]: the original
    subfield M in 3.4.8(8), p. 329,
    specified by closure laws. Its field
    carrier and inclusion are proved to exist. *)
Record is_commutative_subfield (L:fieldType) (S:set L):Prop:={
  (** Source for [commutative_subfield_ring]: the
      original subfield is a subring, p. 329. *)
  commutative_subfield_ring:is_commutative_subring S;
  (** Source for [commutative_subfield_inverse]: the
      original subfield is closed under inverses,
      p. 329, including the field convention at zero. *)
  commutative_subfield_inverse:forall x:L,S x ->S x^-1
}.
