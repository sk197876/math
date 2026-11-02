(** Federer (1969), 2.3.2, p. 74, countable supremum paragraph: the upper
    envelope is defined on the intersection of the domains and takes the
    supremum of the pointwise values. We specify it by upper-bound and
    least-upper-bound laws; the countability assumption belongs to the
    measurability theorem, not the definition. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_function_common_domain]: direct domain
    intersection for the infimum and supremum in Federer 2.3.2,
    p. 74. The intersection over an empty family is the whole source. *)
Definition partial_function_common_domain (X Y J : Type) (D : set J)
    (f : J -> partial_function X Y) : set X :=
  \bigcap_(j in D) partial_function_domain (f j).

(** Source for [partial_function_family_values]: supporting
    pointwise value set whose supremum is taken in Federer
    2.3.2, p. 74, countable-family paragraph. *)
Definition partial_function_family_values (X Y J : Type) (D : set J)
    (f : J -> partial_function X Y) (x : X) : set Y :=
  [set y | exists j, D j /\ partial_function_graph (f j) x y].

(** Source for [is_partial_function_supremum]: abstract direct
    specification of the upper envelope in Federer 2.3.2, p. 74,
    using the supremum laws of 2.1.1, p. 51. *)
Record is_partial_function_supremum (R : realType) (X J : Type) (D : set J)
    (f : J -> partial_function X (extended_real_line R))
    (g : partial_function X (extended_real_line R)) : Prop := {
  (** Source for [partial_function_supremum_domain]: the common
      domain displayed in Federer 2.3.2, p. 74. *)
  partial_function_supremum_domain : partial_function_domain g = partial_function_common_domain D f;
  (** Source for [partial_function_supremum_upper]: the pointwise
      upper-bound law in Federer 2.3.2, p. 74, from 2.1.1, p. 51. *)
  partial_function_supremum_upper : forall x y, partial_function_graph g x y ->
    forall z, partial_function_family_values D f x z -> z <= y;
  (** Source for [partial_function_supremum_least]: the pointwise
      least-upper-bound law in Federer 2.3.2, p. 74, from 2.1.1, p. 51. *)
  partial_function_supremum_least : forall x y, partial_function_graph g x y ->
    forall b, (forall z, partial_function_family_values D f x z -> z <= b) -> y <= b
}.
