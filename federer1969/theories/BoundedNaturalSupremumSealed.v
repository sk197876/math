(** Federer (1969), 3.4.10, p. 337:
    opaque finite-dimensional supremum after proved existence
    and uniqueness. No maximizing point is exposed. *)
From mathcomp Require Import all_boot boolp classical_sets.
From Federer Require Import BoundedNaturalSupremumUP BoundedNaturalSupremumExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Module Type BoundedNaturalSupremumSignature.
(** Source for [value]: the supremum of the
    original bounded local dimensions, 3.4.10, p. 337. *)
Parameter value:forall (X:Type) (S:set X) (q:X->nat) n,
  (forall x,S x ->(q x<=n)%N)->nat.
(** Source for [laws]: independent attained-supremum laws,
    3.4.10, p. 337, for the opaque value. *)
Parameter laws:forall (X:Type) (S:set X) (q:X->nat) n
  (h:forall x,S x ->(q x<=n)%N),
  is_bounded_natural_supremum S q (@value X S q n h).
End BoundedNaturalSupremumSignature.
Module BoundedNaturalSupremum:BoundedNaturalSupremumSignature.
(** Source for [value]: private choice from proved
    existence of the supremum, 3.4.10, p. 337. *)
Definition value (X:Type) (S:set X) (q:X->nat) n
    (h:forall x,S x ->(q x<=n)%N):=
  projT1 (cid (@bounded_natural_supremum_exists X S q n h)).
(** Source for [laws]: the privately selected supremum
    satisfies the original independent laws, 3.4.10, p. 337. *)
Lemma laws (X:Type) (S:set X) (q:X->nat) n
    (h:forall x,S x ->(q x<=n)%N):
  is_bounded_natural_supremum S q (@value X S q n h).
Proof. exact:(projT2 (cid (@bounded_natural_supremum_exists X S q n h))). Qed.
End BoundedNaturalSupremum.
