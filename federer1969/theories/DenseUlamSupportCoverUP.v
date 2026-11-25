(** Federer (1969), 2.2.16, p. 71: abstract open null cover H of the
    complement of the support, with Ulam index cardinality. *)
From mathcomp Require Import all_boot all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import UlamCardinalUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_ulam_open_null_cover]: direct laws
    of the family H in Federer 2.2.16, p. 71:
    open null members, the stated union, and an Ulam
    bound on the indexing set. Repeated members are permitted. *)
Record is_ulam_open_null_cover (R : realType) (X : topologicalType) (J : choiceType)
    (mu : set X -> \bar R) (A : set X) (D : set J) (U : J -> set X) : Prop := {
  ulam_open_cover_indices : is_ulam_set R D;
  ulam_open_cover_open : forall j, D j -> open (U j);
  ulam_open_cover_null : forall j, D j -> mu (U j) = 0;
  ulam_open_cover_union : (\bigcup_(j in D) U j) = A
}.
