(** Federer (1969), 3.4.10, p. 337:
    independent finite-dimensional supremum laws. The empty-set
    value is an explicit auxiliary totalization; it does
    not assign a dimension to an empty variety germ. *)
From mathcomp Require Import all_boot boolp classical_sets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [is_bounded_natural_supremum]: the supremum
    defining dimension in 3.4.10, p. 337,
    specified by upper bounds, attainment when nonempty,
    and an explicit empty-set normalization. *)
Record is_bounded_natural_supremum (X:Type) (S:set X) (q:X->nat) (d:nat):Prop:={
  (** Source for [bounded_natural_supremum_upper]: every
      original local dimension is at most the global
      dimension, 3.4.10, p. 337. *)
  bounded_natural_supremum_upper:forall x,S x ->(q x<=d)%N;
  (** Source for [bounded_natural_supremum_attained]: a nonempty
      bounded natural dimension family attains its supremum,
      as used in 3.4.10, p. 337. *)
  bounded_natural_supremum_attained:S<>set0 ->exists x,S x /\q x=d;
  (** Source for [bounded_natural_supremum_empty]: explicit
      auxiliary totalization at the empty family, supporting
      3.4.10, p. 337. No empty-germ dimension
      is asserted. *)
  bounded_natural_supremum_empty:S=set0 ->d=0%N
}.
