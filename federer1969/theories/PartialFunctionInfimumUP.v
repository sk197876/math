(** Federer (1969), 2.3.2, p. 74, countable infimum paragraph: the lower
    envelope is defined on the intersection of the domains and takes the
    infimum of the pointwise values. We specify it by lower-bound and
    greatest-lower-bound laws; the countability assumption belongs to the
    measurability theorem, not the definition. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP ExtendedRealOrderTopology PartialFunctionSupremumUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [is_partial_function_infimum]: abstract direct
    specification of the lower envelope in Federer 2.3.2, p. 74,
    using the infimum laws of 2.1.1, p. 51. *)
Record is_partial_function_infimum (R : realType) (X J : Type) (D : set J)
    (f : J -> partial_function X (extended_real_line R))
    (g : partial_function X (extended_real_line R)) : Prop := {
  (** Source for [partial_function_infimum_domain]: the common
      domain displayed in Federer 2.3.2, p. 74. *)
  partial_function_infimum_domain : partial_function_domain g = partial_function_common_domain D f;
  (** Source for [partial_function_infimum_lower]: the pointwise
      lower-bound law in Federer 2.3.2, p. 74, from 2.1.1, p. 51. *)
  partial_function_infimum_lower : forall x y, partial_function_graph g x y ->
    forall z, partial_function_family_values D f x z -> y <= z;
  (** Source for [partial_function_infimum_greatest]: the pointwise
      greatest-lower-bound law in Federer 2.3.2, p. 74, from 2.1.1, p. 51. *)
  partial_function_infimum_greatest : forall x y, partial_function_graph g x y ->
    forall b, (forall z, partial_function_family_values D f x z -> b <= z) -> b <= y
}.
