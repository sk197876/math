(** Federer (1969), 2.3.2, p. 74: private existence of the pointwise infimum
    on the common domain. The scalar infimum comes from the already sealed
    2.1.1 interface. Source context and specification:
    PartialFunctionInfimumUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP ExtendedRealOrderTopology ExtendedRealBounds
  PartialFunctionSupremumUP PartialFunctionInfimumUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_function_infimum_witness]: private
    graph construction for the infimum in Federer 2.3.2, p. 74.
    No value is assigned where the common-domain condition fails. *)
Definition partial_function_infimum_witness (R : realType) (X J : Type) (D : set J)
    (f : J -> partial_function X (extended_real_line R)) : partial_function X (extended_real_line R).
Proof.
refine (@Build_partial_function X (extended_real_line R)
  (fun x y => partial_function_common_domain D f x /\
    y = extended_real_inf (partial_function_family_values D f x)) _).
by move=> x y z [_ ->] [_ ->].
Defined.

(** Source for [partial_function_infimum_exists]: existence
    proof for the abstract lower envelope in Federer 2.3.2,
    p. 74. It also applies to empty and uncountable families;
    the later measurability result separately imposes countability. *)
Theorem partial_function_infimum_exists (R : realType) (X J : Type) (D : set J)
    (f : J -> partial_function X (extended_real_line R)) :
  exists g, is_partial_function_infimum D f g.
Proof.
exists (partial_function_infimum_witness D f); constructor.
- apply/seteqP; split=> x.
  + by move=> [y [hx _]].
  + move=> hx; exists (extended_real_inf (partial_function_family_values D f x)); by split.
- move=> x y [_ ->] z hz; exact: extended_real_inf_lower hz.
- move=> x y [_ ->] b hb; exact: extended_real_inf_greatest hb.
Qed.
