(** Federer (1969), 3.2.31, p. 269: independent laws
    for the orthogonal range idempotent used to choose the
    approximating symmetric automorphism. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom SymmetricEndomorphisms.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [is_symmetric_range_idempotent]: supporting
    range-projection specification for the use of 1.7.3 in
    Federer 3.2.31, p. 269. Symmetry, idempotence and the
    exact fixed-point range specify the projection without
    defining it by a selected basis or adjoint construction.
    Existence is separate and no global value is selected. *)
Record is_symmetric_range_idempotent (R:realType) (X Y:lmodType R)
    (B:Y->Y->R) (D:Hom X Y) (P:Hom Y Y):Prop:={
  (** Source for [range_idempotent_symmetric]: supporting
      symmetric range split in 3.2.31, p. 269. *)
  range_idempotent_symmetric:is_symmetric_endomorphism B (hom_as_linear P);
  (** Source for [range_idempotent_idempotent]: supporting
      projection law for the split in 3.2.31, p. 269. *)
  range_idempotent_idempotent:forall y,P (P y)= P y;
  (** Source for [range_idempotent_fixed_range]: the exact
      range of the original map, supporting 3.2.31, p. 269. *)
  range_idempotent_fixed_range:forall y,P y=y <->exists x,D x=y
}.
